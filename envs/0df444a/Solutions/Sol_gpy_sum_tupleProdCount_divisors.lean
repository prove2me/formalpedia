-- Prove2me | solution 1 for gpy_sum_tupleProdCount_divisors
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T20:27:23.208524+00:00
-- url     : https://prove2.me/submissions/416bad5a-4d6b-4b0f-9cf6-c497da709e94

/- Submission file for the Prove2Me problem `gpy_sum_tupleProdCount_divisors` (publish2 fiber batch).
   Self-contained: imports Mathlib only. Contains the verified helper
   bodies needed for the proof, with top-level `theorem solution` in the
   problem's exact binder/statement form (statement mechanically extracted
   from the restated theorem, so the two are textually identical modulo
   the theorem name). No sorry tactic, no axioms beyond the standard
   ones, no platform imports. -/
import Mathlib

open scoped BigOperators
open scoped Function
open Classical

set_option autoImplicit false

namespace GPY

/-- Number of ordered factorizations of `D` into `k` positive factors:
    the `k`-fold divisor function `τ_k(D)` in the form the sums need.
    (Each factor is at most `D` automatically when the product is `D`
    and all factors are positive, so `Icc 1 D` is the right range.) -/
def tupleProdCount (k : ℕ) (D : ℕ) : ℕ :=
  ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 D)).filter
    (fun d => ∏ i, d i = D)).card

/-- The `k`-fold divisor function satisfies the convolution identity
    `τ_{k+1}(D) = ∑_{e ∣ D} τ_k(D/e)`: split a `(k+1)`-tuple at its
    first coordinate. -/
theorem tupleProdCount_succ {k D : ℕ} :
    tupleProdCount (k + 1) D = ∑ e ∈ Nat.divisors D, tupleProdCount k (D / e) := by
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · rw [hD0, Nat.divisors_zero, Finset.sum_empty]
    simp only [tupleProdCount]
    rw [Finset.card_eq_zero]
    ext d
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    intro hd
    have h0 := (Fintype.mem_piFinset.mp hd.1) 0
    rw [Finset.mem_Icc] at h0
    omega
  · have hD1 : 1 ≤ D := hDpos
    -- The defining finset and its first-coordinate fibers.
    set S := (Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 D)).filter
      (fun d => ∏ i, d i = D) with hS
    have hmaps : ∀ d ∈ S, d 0 ∈ Finset.Icc 1 D := by
      intro d hd
      rw [hS] at hd
      rw [Finset.mem_filter, Fintype.mem_piFinset] at hd
      exact hd.1 0
    have hcard : S.card = ∑ e ∈ Finset.Icc 1 D,
        (S.filter (fun d => d 0 = e)).card := by
      rw [Finset.card_eq_sum_card_fiberwise hmaps]
    -- Fiber cards.
    have hfib : ∀ e ∈ Finset.Icc 1 D, (S.filter (fun d => d 0 = e)).card
        = if e ∣ D then tupleProdCount k (D / e) else 0 := by
      intro e he
      rw [Finset.mem_Icc] at he
      by_cases hdiv : e ∣ D
      · rw [if_pos hdiv]
        have hepos : 0 < e := by
          rcases Nat.eq_zero_or_pos e with he0 | hepos
          · omega
          · exact hepos
        have heD : e ≤ D := Nat.le_of_dvd hDpos hdiv
        have hDe : D / e * e = D := Nat.div_mul_cancel hdiv
        have hDe1 : 1 ≤ D / e := by
          rw [Nat.le_div_iff_mul_le hepos]
          simpa using heD
        -- Bijection: tail / cons.
        have hbij : (S.filter (fun d => d 0 = e)).card
            = ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 (D / e))).filter
              (fun t => ∏ i, t i = D / e)).card := by
          apply Finset.card_bij (fun d _ => Fin.tail d)
          · intro d hd
            rw [Finset.mem_filter] at hd ⊢
            obtain ⟨hdS, hd0⟩ := hd
            rw [hS, Finset.mem_filter, Fintype.mem_piFinset] at hdS
            obtain ⟨hdmem, hdprod⟩ := hdS
            have htailprod : ∏ i, Fin.tail d i = D / e := by
              have h1 : ∏ i, d i = d 0 * ∏ i, Fin.tail d i := Fin.prod_univ_succ d
              rw [hd0, hdprod] at h1
              have h2 : e * ∏ i, Fin.tail d i = e * (D / e) := by
                rw [← h1, Nat.mul_div_cancel' hdiv]
              exact Nat.eq_of_mul_eq_mul_left hepos h2
            refine ⟨?_, htailprod⟩
            rw [Fintype.mem_piFinset]
            intro i
            rw [Finset.mem_Icc]
            have hmem : d i.succ ∈ Finset.Icc 1 D := hdmem i.succ
            rw [Finset.mem_Icc] at hmem
            refine ⟨hmem.1, ?_⟩
            have hdvd : d i.succ ∣ ∏ j, Fin.tail d j :=
              Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
            rw [htailprod] at hdvd
            exact Nat.le_of_dvd (by omega : 0 < D / e) hdvd
          · intro d hd e' hd' hde'
            rw [Finset.mem_filter] at hd hd'
            obtain ⟨-, hd0⟩ := hd
            obtain ⟨-, he'0⟩ := hd'
            have hd_eq : d = Fin.cons e (Fin.tail d) := by
              rw [← hd0]; exact (Fin.cons_self_tail d).symm
            have he'_eq : e' = Fin.cons e (Fin.tail e') := by
              rw [← he'0]; exact (Fin.cons_self_tail e').symm
            rw [hd_eq, he'_eq, hde']
          · intro t ht
            rw [Finset.mem_filter, Fintype.mem_piFinset] at ht
            obtain ⟨htmem, htprod⟩ := ht
            refine ⟨Fin.cons e t, ?_, ?_⟩
            · rw [Finset.mem_filter]
              refine ⟨?_, ?_⟩
              · rw [hS, Finset.mem_filter, Fintype.mem_piFinset]
                refine ⟨?_, ?_⟩
                · intro i
                  refine Fin.cases ?_ ?_ i
                  · rw [Fin.cons_zero]
                    exact Finset.mem_Icc.mpr ⟨he.1, heD⟩
                  · intro j
                    rw [Fin.cons_succ]
                    have hmi := htmem j
                    rw [Finset.mem_Icc] at hmi ⊢
                    exact ⟨hmi.1, le_trans hmi.2 (Nat.div_le_self D e)⟩
                · rw [Fin.prod_univ_succ, Fin.cons_zero]
                  simp only [Fin.cons_succ]
                  rw [htprod, Nat.mul_div_cancel' hdiv]
              · rw [Fin.cons_zero]
            · rw [Fin.tail_cons]
        rw [hbij]
        rfl
      · rw [if_neg hdiv]
        rw [Finset.card_eq_zero]
        ext d
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
        intro hd
        obtain ⟨hdS, hd0⟩ := hd
        rw [hS, Finset.mem_filter] at hdS
        obtain ⟨-, hdprod⟩ := hdS
        have h1 : ∏ i, d i = d 0 * ∏ i, Fin.tail d i := Fin.prod_univ_succ d
        rw [hd0, hdprod] at h1
        exact hdiv ⟨∏ i, Fin.tail d i, h1⟩
    have hTS : tupleProdCount (k + 1) D = S.card := rfl
    rw [hTS, hcard]
    rw [Finset.sum_congr rfl hfib]
    rw [← Finset.sum_filter]
    congr 1

/-- Summing `τ_k` over the divisors of `L` gives `τ_{k+1}(L)`: the
    convolution identity plus the divisor involution `D ↦ L / D`. -/
theorem sum_tupleProdCount_divisors {k L : ℕ} (hL : L ≠ 0) :
    ∑ D ∈ L.divisors, tupleProdCount k D = tupleProdCount (k + 1) L := by
  rw [tupleProdCount_succ]
  apply Finset.sum_bij (fun D _ => L / D)
  · intro D hD
    rw [Nat.mem_divisors] at hD ⊢
    exact ⟨⟨D, (Nat.div_mul_cancel hD.1).symm⟩, hL⟩
  · intro a ha b hb hab
    rw [Nat.mem_divisors] at ha hb
    have h1 : a = L / (L / a) := (Nat.div_div_self ha.1 hL).symm
    have h2 : b = L / (L / b) := (Nat.div_div_self hb.1 hL).symm
    rw [h1, h2, hab]
  · intro D hD
    rw [Nat.mem_divisors] at hD
    refine ⟨L / D, ?_, ?_⟩
    · rw [Nat.mem_divisors]
      exact ⟨⟨D, (Nat.div_mul_cancel hD.1).symm⟩, hL⟩
    · exact Nat.div_div_self hD.1 hL
  · intro D hD
    rw [Nat.div_div_self (Nat.mem_divisors.mp hD).1 hL]

theorem sum_tupleProdCount_divisors_restated_pub2 {k L : ℕ} (hL : L ≠ 0) :
    ∑ D ∈ L.divisors,
        ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 D)).filter
          (fun d => ∏ i, d i = D)).card
      = ((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
        (fun d => ∏ i, d i = L)).card := by
  have hmain := sum_tupleProdCount_divisors (k := k) (L := L) hL
  unfold tupleProdCount at hmain
  exact hmain


end GPY

theorem solution {k L : ℕ} (hL : L ≠ 0) :
    ∑ D ∈ L.divisors,
        ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 D)).filter
          (fun d => ∏ i, d i = D)).card
      = ((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
        (fun d => ∏ i, d i = L)).card := GPY.sum_tupleProdCount_divisors_restated_pub2 hL
