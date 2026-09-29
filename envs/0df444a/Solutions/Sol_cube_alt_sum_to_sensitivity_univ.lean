-- Prove2me | solution 1 for cube_alt_sum_to_sensitivity_univ
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-05-06T22:09:28.259732+00:00
-- url     : https://prove2.me/submissions/b7e7858b-7251-4b88-bab7-f32db053433b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_cube_even_weight_count
import Definitions.Def_BoolFunc
import Definitions.Def_Hypercube
import Definitions.Def_sensitivity
import Definitions.Def_Mobius
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# d-cube alternating-sum ⇒ sensitivity bound

Specialised to `Finset.univ : Finset (Fin d)`. If `g : BoolFunc d` has
non-zero top Möbius alternating sum, then `h d ≤ sensitivity g`. This is
the "core" Gotsman–Linial parity step, with the sub-cube bridge stripped
away — the parent theorem `bool_func_alternating_sum_sensitivity`
reduces to this via `Finset.orderEmbOfFin`.

Proof outline (in the sketch):
- Parity-split the alternating sum: it equals `(-1)^d · (A − B)` where
  `A := #{z : g z = true ∧ |z| even}`, `B := #{z : g z = true ∧ |z| odd}`.
  Hence `A ≠ B`.
- WLOG `A > B`. Define the "parity-aligned" majority set
  `H := {z : g z = true ∧ |z| even} ∪ {z : g z = false ∧ |z| odd}`.
  Then `|H| = 2^(d-1) + (A − B) > 2^(d-1)`.
- Apply `hQ` at `m = d` to pick `v ∈ H` with `h d ≤ degreeIn d H v`.
- For `v ∈ H`, every neighbour `u` of `v` satisfies `u ∈ H ↔ g u ≠ g v`
  (parity flips when one bit is flipped). Hence
  `degreeIn d H v = sensitivityAt g v ≤ sensitivity g`.
-/


open Mobius Finset

/-!
# Proof — `cube_alt_sum_to_sensitivity_univ`

The d-cube core of the Gotsman–Linial parity step. Given non-zero alt-sum
on the full cube, build the parity-aligned majority set `H`, apply the
hypercube max-degree hypothesis at `m = d`, and identify
`degreeIn d H v = sensitivityAt g v` via the parity-flip bijection.

Uses `cube_even_weight_count` (child) to know `#{weight z even} = 2^(d-1)`.
-/

namespace CubeAltSum

variable {d : ℕ}

/-- The Hamming weight of a cube vertex (size of its `trueSet`). -/
noncomputable def weight (z : Fin d → Bool) : ℕ :=
  (Mobius.trueSet z).card

@[simp] lemma weight_eq (z : Fin d → Bool) :
    weight z = ((Finset.univ : Finset (Fin d)).filter (fun i => z i)).card := by
  unfold weight Mobius.trueSet
  rfl

/-- `trueSet (boolOfFinset T) = T`. -/
lemma trueSet_boolOfFinset (T : Finset (Fin d)) :
    Mobius.trueSet (Mobius.boolOfFinset T) = T := by
  ext i
  simp only [Mobius.mem_trueSet, Mobius.boolOfFinset_apply]
  constructor
  · intro h
    have : (decide (i ∈ T)) = true := h
    exact of_decide_eq_true this
  · intro h
    exact decide_eq_true h

/-- Cardinality of `boolOfFinset T`'s trueSet equals `T.card`. -/
@[simp] lemma weight_boolOfFinset (T : Finset (Fin d)) :
    weight (Mobius.boolOfFinset T) = T.card := by
  rw [weight, trueSet_boolOfFinset]

/-- Pointwise unfolding of `flipBit`. -/
lemma flipBit_apply (v : Fin d → Bool) (i j : Fin d) :
    flipBit v i j = if j = i then !v i else v j := by
  unfold flipBit
  by_cases hj : j = i
  · subst hj; rw [Function.update_self]; simp
  · rw [Function.update_of_ne hj]; simp [hj]

lemma flipBit_index_injective (v : Fin d → Bool) :
    Function.Injective (fun i : Fin d => flipBit v i) := by
  intro i j h
  dsimp only at h
  by_contra hne
  have hi : (flipBit v i) i = (flipBit v j) i := by rw [h]
  rw [flipBit_apply, flipBit_apply, if_pos rfl, if_neg hne] at hi
  cases v i <;> simp at hi

/-- Flipping a bit changes the trueSet cardinality by ±1, hence parity flips. -/
lemma weight_flipBit_parity_ne (v : Fin d → Bool) (i : Fin d) :
    weight (flipBit v i) % 2 ≠ weight v % 2 := by
  classical
  rw [weight_eq, weight_eq]
  by_cases hv : v i = true
  · have h_eq :
        (Finset.univ : Finset (Fin d)).filter (fun j => flipBit v i j = true)
        = ((Finset.univ : Finset (Fin d)).filter (fun j => v j = true)).erase i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      by_cases hj : j = i
      · subst hj
        rw [flipBit_apply, if_pos rfl, hv]
        simp
      · rw [flipBit_apply, if_neg hj]
        tauto
    have hi_mem :
        i ∈ (Finset.univ : Finset (Fin d)).filter (fun j => v j = true) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hv
    rw [h_eq, Finset.card_erase_of_mem hi_mem]
    have hcard_pos :
        0 < ((Finset.univ : Finset (Fin d)).filter (fun j => v j = true)).card :=
      Finset.card_pos.mpr ⟨_, hi_mem⟩
    omega
  · have hv_false : v i = false := by
      cases h : v i
      · rfl
      · exact absurd h hv
    have h_eq :
        (Finset.univ : Finset (Fin d)).filter (fun j => flipBit v i j = true)
        = insert i ((Finset.univ : Finset (Fin d)).filter (fun j => v j = true)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      by_cases hj : j = i
      · subst hj
        rw [flipBit_apply, if_pos rfl, hv_false]
        simp
      · rw [flipBit_apply, if_neg hj]
        tauto
    have hi_notmem :
        i ∉ (Finset.univ : Finset (Fin d)).filter (fun j => v j = true) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hv_false]; simp
    rw [h_eq, Finset.card_insert_of_notMem hi_notmem]
    omega

/-- `Adj d u v ↔ ∃ i, u = flipBit v i`. -/
lemma adj_iff_eq_flipBit (u v : Fin d → Bool) :
    Hypercube.Adj d u v ↔ ∃ i, u = flipBit v i := by
  unfold Hypercube.Adj
  constructor
  · intro h
    rw [Finset.card_eq_one] at h
    obtain ⟨i, hi⟩ := h
    refine ⟨i, ?_⟩
    funext j
    rw [flipBit_apply]
    by_cases hj : j = i
    · rw [if_pos hj]
      have hi_in : i ∈ (Finset.univ : Finset (Fin d)).filter (fun k => u k ≠ v k) := by
        rw [hi]; exact Finset.mem_singleton.mpr rfl
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi_in
      rw [hj]
      cases hu : u i <;> cases hv : v i <;> simp_all
    · rw [if_neg hj]
      have hj_notin : j ∉ (Finset.univ : Finset (Fin d)).filter (fun k => u k ≠ v k) := by
        rw [hi]; intro h1; exact hj (Finset.mem_singleton.mp h1)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj_notin
      exact hj_notin
  · rintro ⟨i, rfl⟩
    rw [show (Finset.univ : Finset (Fin d)).filter (fun j => flipBit v i j ≠ v j) = {i}
          from ?_]
    · rfl
    · ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [flipBit_apply]
      by_cases hj : j = i
      · rw [if_pos hj, hj]; cases v i <;> simp
      · rw [if_neg hj]
        constructor
        · intro hne; exact absurd rfl hne
        · intro h_eq; exact absurd h_eq hj

/-- The set of S-vertices adjacent to v equals the image of `flipBit v ·`
    on the indices i for which `flipBit v i ∈ S`. -/
lemma filter_adj_eq_image_flipBit (S : Finset (Fin d → Bool)) (v : Fin d → Bool) :
    S.filter (fun u => Hypercube.Adj d u v)
    = ((Finset.univ : Finset (Fin d)).filter (fun i => flipBit v i ∈ S)).image
        (fun i => flipBit v i) := by
  classical
  ext u
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hu_S, hu_adj⟩
    obtain ⟨i, rfl⟩ := (adj_iff_eq_flipBit u v).mp hu_adj
    exact ⟨i, hu_S, rfl⟩
  · rintro ⟨i, hi_in, rfl⟩
    refine ⟨hi_in, ?_⟩
    exact (adj_iff_eq_flipBit (flipBit v i) v).mpr ⟨i, rfl⟩

/-- `degreeIn d S v = #{i : flipBit v i ∈ S}`. -/
lemma degreeIn_eq_filter_flipBit_card (S : Finset (Fin d → Bool)) (v : Fin d → Bool) :
    Hypercube.degreeIn d S v
    = ((Finset.univ : Finset (Fin d)).filter (fun i => flipBit v i ∈ S)).card := by
  classical
  unfold Hypercube.degreeIn
  rw [filter_adj_eq_image_flipBit]
  rw [Finset.card_image_of_injOn]
  intros i _ j _ h
  exact flipBit_index_injective v h

end CubeAltSum

theorem solution
    (h : ℕ → ℝ) (hmono : Monotone h)
    (hQ : ∀ m, 0 < m → ∀ S : Finset (Fin m → Bool),
        2 ^ (m - 1) < S.card →
          ∃ v ∈ S, h m ≤ (Hypercube.degreeIn m S v : ℝ))
    {d : ℕ} (h_pos : 1 ≤ d) (g : BoolFunc d)
    (h_alt :
      (∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
          (if (d - T.card) % 2 = 0 then (1 : ℝ) else -1) *
          (if g (fun i => decide (i ∈ T)) then (1 : ℝ) else 0))
        ≠ 0) :
    h d ≤ (sensitivity g : ℝ) := by
  classical
  -- Step 1: convert h_alt to Mobius.altSum form.
  have h_unfold : ∀ S : Finset (Fin d),
      (∑ T ∈ S.powerset,
          (if (S.card - T.card) % 2 = 0 then (1 : ℝ) else -1) *
          (if g (fun i => decide (i ∈ T)) then (1 : ℝ) else 0))
        = Mobius.altSum g S := by
    intro S
    unfold Mobius.altSum Mobius.signR Mobius.realOf Mobius.boolOfFinset
    rfl
  have h_univ_card : (Finset.univ : Finset (Fin d)).card = d := by
    rw [Finset.card_univ, Fintype.card_fin]
  have h_alt' : Mobius.altSum g (Finset.univ : Finset (Fin d)) ≠ 0 := by
    rw [← h_unfold (Finset.univ : Finset (Fin d))]
    convert h_alt using 2
    rw [h_univ_card]
  -- Step 2: pull out signR(d) factor and reindex T ↔ z.
  -- altSum g univ = signR d * ∑ z, signR(weight z) * realOf(g z).
  set sumZ : ℝ :=
    ∑ z ∈ (Finset.univ : Finset (Fin d → Bool)),
      Mobius.signR (CubeAltSum.weight z) * Mobius.realOf (g z) with sumZ_def
  have h_factor : Mobius.altSum g (Finset.univ : Finset (Fin d)) =
      Mobius.signR d * sumZ := by
    calc Mobius.altSum g (Finset.univ : Finset (Fin d))
        = ∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
            Mobius.signR ((Finset.univ : Finset (Fin d)).card - T.card) *
              Mobius.realOf (g (Mobius.boolOfFinset T)) := rfl
      _ = ∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
            Mobius.signR (d - T.card) *
              Mobius.realOf (g (Mobius.boolOfFinset T)) := by
          rw [h_univ_card]
      _ = ∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
            Mobius.signR d * Mobius.signR T.card *
              Mobius.realOf (g (Mobius.boolOfFinset T)) := by
          apply Finset.sum_congr rfl
          intro T hT
          have hT_card_le : T.card ≤ d := by
            have h₁ : T.card ≤ (Finset.univ : Finset (Fin d)).card :=
              Finset.card_le_card (Finset.mem_powerset.mp hT)
            linarith [h_univ_card]
          rw [Mobius.signR_sub_of_le hT_card_le]
      _ = Mobius.signR d * ∑ T ∈ (Finset.univ : Finset (Fin d)).powerset,
            Mobius.signR T.card * Mobius.realOf (g (Mobius.boolOfFinset T)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intros
          ring
      _ = Mobius.signR d * sumZ := by
          rw [sumZ_def]
          congr 1
          refine Finset.sum_bij' (fun T _ => Mobius.boolOfFinset T)
                                 (fun z _ => Mobius.trueSet z) ?_ ?_ ?_ ?_ ?_
          · intro T _; exact Finset.mem_univ _
          · intro z _; exact Finset.mem_powerset.mpr (Finset.subset_univ _)
          · intro T _; exact CubeAltSum.trueSet_boolOfFinset T
          · intro z _; exact Mobius.boolOfFinset_trueSet z
          · intro T _; rw [CubeAltSum.weight_boolOfFinset]
  -- Step 3: split sumZ = (Aev : ℝ) - (Bod : ℝ).
  set Aev : ℕ := ((Finset.univ : Finset (Fin d → Bool)).filter
    (fun z => g z = true ∧ CubeAltSum.weight z % 2 = 0)).card with Aev_def
  set Bod : ℕ := ((Finset.univ : Finset (Fin d → Bool)).filter
    (fun z => g z = true ∧ CubeAltSum.weight z % 2 = 1)).card with Bod_def
  have h_sumZ_eq : sumZ = (Aev : ℝ) - (Bod : ℝ) := by
    rw [sumZ_def]
    have key : ∀ z : Fin d → Bool,
        Mobius.signR (CubeAltSum.weight z) * Mobius.realOf (g z) =
        (if g z = true ∧ CubeAltSum.weight z % 2 = 0 then (1 : ℝ) else 0) -
        (if g z = true ∧ CubeAltSum.weight z % 2 = 1 then (1 : ℝ) else 0) := by
      intro z
      by_cases hg : g z = true
      · have hreal : Mobius.realOf (g z) = 1 := by rw [hg]; exact Mobius.realOf_true
        rw [hreal, mul_one]
        by_cases hp : CubeAltSum.weight z % 2 = 0
        · have hsig : Mobius.signR (CubeAltSum.weight z) = 1 := by
            unfold Mobius.signR; exact if_pos hp
          rw [hsig, if_pos ⟨hg, hp⟩]
          have hp_not1 : ¬ CubeAltSum.weight z % 2 = 1 := by omega
          rw [if_neg (fun h => hp_not1 h.2)]
          ring
        · have hp1 : CubeAltSum.weight z % 2 = 1 := by omega
          have hsig : Mobius.signR (CubeAltSum.weight z) = -1 := by
            unfold Mobius.signR; exact if_neg hp
          rw [hsig, if_neg (fun h => hp h.2), if_pos ⟨hg, hp1⟩]
          ring
      · have hg_false : g z = false := by
          cases h : g z
          · rfl
          · exact absurd h hg
        have hreal : Mobius.realOf (g z) = 0 := by
          rw [hg_false]; exact Mobius.realOf_false
        rw [hreal, mul_zero, if_neg (fun h => hg h.1), if_neg (fun h => hg h.1)]
        ring
    rw [Finset.sum_congr rfl (fun z _ => key z)]
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_boole, Finset.sum_boole]
  -- Step 4: Aev ≠ Bod.
  have h_signR_d_ne : Mobius.signR d ≠ 0 := by
    rw [Mobius.signR_eq_neg_one_pow]
    exact pow_ne_zero d (by norm_num : (-1 : ℝ) ≠ 0)
  have h_diff_ne : (Aev : ℝ) - (Bod : ℝ) ≠ 0 := by
    intro heq
    apply h_alt'
    rw [h_factor, h_sumZ_eq, heq, mul_zero]
  have h_Aev_ne_Bod : Aev ≠ Bod := by
    intro heq
    apply h_diff_ne
    rw [heq]; ring
  -- Step 5: parity counts via cube_even_weight_count.
  set Cev : ℕ := ((Finset.univ : Finset (Fin d → Bool)).filter
    (fun z => g z = false ∧ CubeAltSum.weight z % 2 = 0)).card with Cev_def
  set Dod : ℕ := ((Finset.univ : Finset (Fin d → Bool)).filter
    (fun z => g z = false ∧ CubeAltSum.weight z % 2 = 1)).card with Dod_def
  -- #even = 2^(d-1) from child theorem.
  have h_even_count :
      ((Finset.univ : Finset (Fin d → Bool)).filter
        (fun z => CubeAltSum.weight z % 2 = 0)).card = 2^(d-1) := by
    exact cube_even_weight_count h_pos (d := d)
  -- A reusable lemma: |{g=true ∧ p}| + |{g=false ∧ p}| = |{p}|.
  have h_split_by_g : ∀ (p : (Fin d → Bool) → Prop) [DecidablePred p],
      ((Finset.univ : Finset (Fin d → Bool)).filter
        (fun z => g z = true ∧ p z)).card +
      ((Finset.univ : Finset (Fin d → Bool)).filter
        (fun z => g z = false ∧ p z)).card =
      ((Finset.univ : Finset (Fin d → Bool)).filter p).card := by
    intro p _
    rw [show ((Finset.univ : Finset (Fin d → Bool)).filter p)
          = ((Finset.univ : Finset (Fin d → Bool)).filter
              (fun z => g z = true ∧ p z))
          ∪ ((Finset.univ : Finset (Fin d → Bool)).filter
              (fun z => g z = false ∧ p z)) from ?_]
    · rw [Finset.card_union_of_disjoint]
      apply Finset.disjoint_filter.mpr
      intros z _ h₁ h₂
      rw [h₁.1] at h₂
      exact Bool.noConfusion h₂.1
    · ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      constructor
      · intro hp
        by_cases hg : g z = true
        · left; exact ⟨hg, hp⟩
        · have hg_false : g z = false := by
            cases h : g z
            · rfl
            · exact absurd h hg
          right; exact ⟨hg_false, hp⟩
      · rintro (⟨_, hp⟩ | ⟨_, hp⟩) <;> exact hp
  -- Aev + Cev = #even = 2^(d-1).
  have h_AC : Aev + Cev = 2^(d-1) := by
    rw [Aev_def, Cev_def, h_split_by_g]
    exact h_even_count
  -- #odd = 2^(d-1) via complement.
  have h_odd_count :
      ((Finset.univ : Finset (Fin d → Bool)).filter
        (fun z => CubeAltSum.weight z % 2 = 1)).card = 2^(d-1) := by
    have h_partition :
        ((Finset.univ : Finset (Fin d → Bool)).filter
          (fun z => CubeAltSum.weight z % 2 = 0)).card
        + ((Finset.univ : Finset (Fin d → Bool)).filter
            (fun z => CubeAltSum.weight z % 2 = 1)).card
        = (Finset.univ : Finset (Fin d → Bool)).card := by
      rw [show ((Finset.univ : Finset (Fin d → Bool)).filter
                (fun z => CubeAltSum.weight z % 2 = 1))
            = ((Finset.univ : Finset (Fin d → Bool)).filter
                (fun z => ¬ CubeAltSum.weight z % 2 = 0)) from
          Finset.filter_congr (fun _ _ => by omega)]
      exact Finset.card_filter_add_card_filter_not _
    rw [h_even_count] at h_partition
    have h_univ : (Finset.univ : Finset (Fin d → Bool)).card = 2^d := by
      rw [Finset.card_univ, Fintype.card_pi_const, Fintype.card_bool]
    rw [h_univ] at h_partition
    have hd_split : 2^d = 2 * 2^(d-1) := by
      obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
      rw [Nat.add_sub_cancel, pow_succ, mul_comm]
    omega
  -- Bod + Dod = #odd = 2^(d-1).
  have h_BD : Bod + Dod = 2^(d-1) := by
    rw [Bod_def, Dod_def, h_split_by_g]
    exact h_odd_count
  -- Step 6-9: case split on Aev vs Bod.
  rcases lt_or_gt_of_ne h_Aev_ne_Bod with h_lt | h_gt
  · -- Case 1: Aev < Bod. H := {g=true ∧ odd} ∪ {g=false ∧ even}.
    set H : Finset (Fin d → Bool) :=
      (Finset.univ : Finset (Fin d → Bool)).filter
        (fun z => (g z = true ∧ CubeAltSum.weight z % 2 = 1) ∨
                  (g z = false ∧ CubeAltSum.weight z % 2 = 0)) with H_def
    -- |H| = Bod + Cev > 2^(d-1).
    have h_H_card : H.card = Bod + Cev := by
      rw [H_def]
      rw [show ((Finset.univ : Finset (Fin d → Bool)).filter
                (fun z => (g z = true ∧ CubeAltSum.weight z % 2 = 1) ∨
                          (g z = false ∧ CubeAltSum.weight z % 2 = 0)))
            = ((Finset.univ : Finset (Fin d → Bool)).filter
                (fun z => g z = true ∧ CubeAltSum.weight z % 2 = 1))
              ∪ ((Finset.univ : Finset (Fin d → Bool)).filter
                  (fun z => g z = false ∧ CubeAltSum.weight z % 2 = 0)) from
          Finset.filter_or _ _ _]
      rw [Finset.card_union_of_disjoint, Bod_def, Cev_def]
      · -- disjointness
        apply Finset.disjoint_filter.mpr
        intros z _ h₁ h₂
        rw [h₁.1] at h₂
        exact Bool.noConfusion h₂.1
    have h_H_gt : 2^(d-1) < H.card := by
      rw [h_H_card]
      have h_AC' : Aev + Cev = 2^(d-1) := h_AC
      omega
    -- Apply hQ.
    obtain ⟨v, hv_mem, hv_bound⟩ := hQ d (by omega) H h_H_gt
    -- Parity bijection: degreeIn d H v = sensitivityAt g v.
    have hv_unfold : (g v = true ∧ CubeAltSum.weight v % 2 = 1) ∨
                     (g v = false ∧ CubeAltSum.weight v % 2 = 0) := by
      simp only [H_def, Finset.mem_filter, Finset.mem_univ, true_and] at hv_mem
      exact hv_mem
    have h_flip_iff : ∀ i : Fin d,
        flipBit v i ∈ H ↔ g (flipBit v i) ≠ g v := by
      intro i
      have hpar : CubeAltSum.weight (flipBit v i) % 2 ≠ CubeAltSum.weight v % 2 :=
        CubeAltSum.weight_flipBit_parity_ne v i
      simp only [H_def, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hv_unfold with ⟨hg_v, hp_v⟩ | ⟨hg_v, hp_v⟩
      · -- g v = true, weight v % 2 = 1.
        rw [hg_v]; rw [hp_v] at hpar
        have hp_flip : CubeAltSum.weight (flipBit v i) % 2 = 0 := by omega
        constructor
        · rintro (⟨_, h⟩ | ⟨h, _⟩)
          · omega
          · rw [h]; simp
        · intro h
          have hg_flip : g (flipBit v i) = false := by
            cases hh : g (flipBit v i)
            · rfl
            · rw [hh] at h; exact absurd rfl h
          right; exact ⟨hg_flip, hp_flip⟩
      · -- g v = false, weight v % 2 = 0.
        rw [hg_v]; rw [hp_v] at hpar
        have hp_flip : CubeAltSum.weight (flipBit v i) % 2 = 1 := by omega
        constructor
        · rintro (⟨h, _⟩ | ⟨_, h⟩)
          · rw [h]; simp
          · omega
        · intro h
          have hg_flip : g (flipBit v i) = true := by
            cases hh : g (flipBit v i)
            · rw [hh] at h; exact absurd rfl h
            · rfl
          left; exact ⟨hg_flip, hp_flip⟩
    have h_deg_eq_sens : Hypercube.degreeIn d H v = sensitivityAt g v := by
      rw [CubeAltSum.degreeIn_eq_filter_flipBit_card]
      unfold sensitivityAt
      apply Finset.card_bij (fun i _ => i)
      · intros i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact (h_flip_iff i).mp hi
      · intros i _ j _ h; exact h
      · intros i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        refine ⟨i, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (h_flip_iff i).mpr hi
    -- Conclude h d ≤ sensitivity g.
    have h_sens_at : (sensitivityAt g v : ℝ) ≤ (sensitivity g : ℝ) := by
      exact_mod_cast Finset.le_sup (f := sensitivityAt g) (Finset.mem_univ v)
    calc (h d : ℝ)
        ≤ (Hypercube.degreeIn d H v : ℝ) := hv_bound
      _ = (sensitivityAt g v : ℝ) := by exact_mod_cast h_deg_eq_sens
      _ ≤ (sensitivity g : ℝ) := h_sens_at
  · -- Case 2: Aev > Bod. H := {g=true ∧ even} ∪ {g=false ∧ odd}.
    set H : Finset (Fin d → Bool) :=
      (Finset.univ : Finset (Fin d → Bool)).filter
        (fun z => (g z = true ∧ CubeAltSum.weight z % 2 = 0) ∨
                  (g z = false ∧ CubeAltSum.weight z % 2 = 1)) with H_def
    have h_H_card : H.card = Aev + Dod := by
      rw [H_def]
      rw [show ((Finset.univ : Finset (Fin d → Bool)).filter
                (fun z => (g z = true ∧ CubeAltSum.weight z % 2 = 0) ∨
                          (g z = false ∧ CubeAltSum.weight z % 2 = 1)))
            = ((Finset.univ : Finset (Fin d → Bool)).filter
                (fun z => g z = true ∧ CubeAltSum.weight z % 2 = 0))
              ∪ ((Finset.univ : Finset (Fin d → Bool)).filter
                  (fun z => g z = false ∧ CubeAltSum.weight z % 2 = 1)) from
          Finset.filter_or _ _ _]
      rw [Finset.card_union_of_disjoint, Aev_def, Dod_def]
      · apply Finset.disjoint_filter.mpr
        intros z _ h₁ h₂
        rw [h₁.1] at h₂
        exact Bool.noConfusion h₂.1
    have h_H_gt : 2^(d-1) < H.card := by
      rw [h_H_card]
      have h_BD' : Bod + Dod = 2^(d-1) := h_BD
      omega
    obtain ⟨v, hv_mem, hv_bound⟩ := hQ d (by omega) H h_H_gt
    have hv_unfold : (g v = true ∧ CubeAltSum.weight v % 2 = 0) ∨
                     (g v = false ∧ CubeAltSum.weight v % 2 = 1) := by
      simp only [H_def, Finset.mem_filter, Finset.mem_univ, true_and] at hv_mem
      exact hv_mem
    have h_flip_iff : ∀ i : Fin d,
        flipBit v i ∈ H ↔ g (flipBit v i) ≠ g v := by
      intro i
      have hpar : CubeAltSum.weight (flipBit v i) % 2 ≠ CubeAltSum.weight v % 2 :=
        CubeAltSum.weight_flipBit_parity_ne v i
      simp only [H_def, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hv_unfold with ⟨hg_v, hp_v⟩ | ⟨hg_v, hp_v⟩
      · -- g v = true, weight v % 2 = 0.
        rw [hg_v]; rw [hp_v] at hpar
        have hp_flip : CubeAltSum.weight (flipBit v i) % 2 = 1 := by omega
        constructor
        · rintro (⟨_, h⟩ | ⟨h, _⟩)
          · omega
          · rw [h]; simp
        · intro h
          have hg_flip : g (flipBit v i) = false := by
            cases hh : g (flipBit v i)
            · rfl
            · rw [hh] at h; exact absurd rfl h
          right; exact ⟨hg_flip, hp_flip⟩
      · -- g v = false, weight v % 2 = 1.
        rw [hg_v]; rw [hp_v] at hpar
        have hp_flip : CubeAltSum.weight (flipBit v i) % 2 = 0 := by omega
        constructor
        · rintro (⟨h, _⟩ | ⟨_, h⟩)
          · rw [h]; simp
          · omega
        · intro h
          have hg_flip : g (flipBit v i) = true := by
            cases hh : g (flipBit v i)
            · rw [hh] at h; exact absurd rfl h
            · rfl
          left; exact ⟨hg_flip, hp_flip⟩
    have h_deg_eq_sens : Hypercube.degreeIn d H v = sensitivityAt g v := by
      rw [CubeAltSum.degreeIn_eq_filter_flipBit_card]
      unfold sensitivityAt
      apply Finset.card_bij (fun i _ => i)
      · intros i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        exact (h_flip_iff i).mp hi
      · intros i _ j _ h; exact h
      · intros i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        refine ⟨i, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (h_flip_iff i).mpr hi
    have h_sens_at : (sensitivityAt g v : ℝ) ≤ (sensitivity g : ℝ) := by
      exact_mod_cast Finset.le_sup (f := sensitivityAt g) (Finset.mem_univ v)
    calc (h d : ℝ)
        ≤ (Hypercube.degreeIn d H v : ℝ) := hv_bound
      _ = (sensitivityAt g v : ℝ) := by exact_mod_cast h_deg_eq_sens
      _ ≤ (sensitivity g : ℝ) := h_sens_at
