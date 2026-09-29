-- Prove2me | solution 1 for input_valuation_equidistribution_counterexample_unfolded
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-29T03:44:27.360873+00:00
-- url     : https://prove2.me/submissions/f267af22-94c2-438c-8cc5-51852940992f

import Mathlib
import Definitions.Def_syracuseOrbitMin

set_option autoImplicit false

noncomputable section

attribute [instance] Classical.propDecidable

-- NOTE (2026-09-29 unfolded-node probe): this submission defines NO local
-- helper defs. The target node
-- `input_valuation_equidistribution_counterexample_unfolded` is self-contained:
-- its statement unfolds `valVec`/`syrVal` into import-only identifiers
-- (`syracuseStep`, `Nat.factorization`), so there is nothing to redefine
-- (redefinition -> verifier WA on preamble-def collision) and nothing missing
-- (omission of preamble defs -> verifier CE, submissions elaborate without
-- the node preamble in scope). Every identifier below resolves from the two
-- imports above.
/-- Positively-phrased counterexample for `input_valuation_equidistribution`
    (`cf32ac58-dc23-436e-874f-578f99027eea`, tao-collatz mission), in unfolded
    self-contained form.

    The witness is `n₀ = 1`, `m = 1`, `ā ≡ 1`. All hypotheses hold
    (`1 ≤ 1`; every entry `≥ 1`; `∑ā = 1 ≤ 1 = m`), but
    `Finset.range (2^1) = {0, 1}` contributes nothing to the filter:
    - `r = 0` is not odd;
    - `r = 1` is odd, but the valuation vector at `r = 1` is
      `(fun _ => 2)`, since at the unique `j : Fin 1`,
      `Nat.factorization (3 * syracuseStep^[j.val] 1 + 1) 2
        = Nat.factorization 4 2 = 2 ≠ 1 = ā j`.
    Hence the filtered card is `0`, while the claimed RHS is `2^(1-1) = 1`. -/
theorem solution : ∃ (n₀ m : ℕ) (ā : Fin n₀ → ℕ),
      1 ≤ n₀ ∧ (∀ j, 1 ≤ ā j) ∧ Finset.sum Finset.univ (fun j => ā j) ≤ m ∧
        (Finset.filter (fun r => Odd r ∧ (fun j => Nat.factorization (3 * syracuseStep^[j.val] r + 1) 2) = ā) (Finset.range (2 ^ m))).card
          ≠ 2 ^ (m - Finset.sum Finset.univ (fun j => ā j)) := by
  refine ⟨1, 1, (fun _ : Fin 1 => (1 : ℕ)), le_rfl, (fun j => le_rfl), by simp, ?_⟩
  intro heq
  have hempty : Finset.filter (fun r => Odd r ∧ (fun j => Nat.factorization (3 * syracuseStep^[j.val] r + 1) 2) = (fun _ : Fin 1 => (1 : ℕ)))
      (Finset.range (2 ^ 1)) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨hrlt, hodd, hval⟩ := hr
    have hr2 : r < 2 := lt_of_lt_of_le hrlt (by norm_num)
    interval_cases r
    · obtain ⟨k, hk⟩ := hodd
      omega
    · have h2 := congrFun hval ⟨0, by norm_num⟩
      have hcon : Nat.factorization (3 * 1 + 1) 2 = 1 := h2
      have hsyr1 : Nat.factorization (3 * 1 + 1) 2 = 2 := by
        have hfact : Nat.factorization (3 * 1 + 1) 2 = 2 := by
          rw [show (3 : ℕ) * 1 + 1 = 4 from by norm_num,
            Nat.factorization_def 4 (by norm_num)]
          have h1dvd : (2 : ℕ) ^ 2 ∣ 4 := by decide
          have h2dvd : ¬ (2 : ℕ) ^ 3 ∣ 4 := by decide
          have g1 : 2 ≤ padicValNat 2 4 :=
            (Nat.pow_dvd_iff_le_padicValNat (p := 2) (k := 2) (n := 4) (by norm_num)
              (by norm_num)).mp h1dvd
          have g2 : ¬ 3 ≤ padicValNat 2 4 := fun hle =>
            h2dvd ((Nat.pow_dvd_iff_le_padicValNat (p := 2) (k := 3) (n := 4) (by norm_num)
              (by norm_num)).mpr hle)
          omega
        exact hfact
      omega
  rw [hempty, Finset.card_empty] at heq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul] at heq
  norm_num at heq

/-- Alias under the published node name: the platform verifier looks up the
    published theorem name in the submission environment (dual-naming fix,
    cf. input_syracuse_odd_preserving ACCEPTED 2026-09-29). -/
theorem input_valuation_equidistribution_counterexample_unfolded :
    ∃ (n₀ m : ℕ) (ā : Fin n₀ → ℕ),
      1 ≤ n₀ ∧ (∀ j, 1 ≤ ā j) ∧ Finset.sum Finset.univ (fun j => ā j) ≤ m ∧
        (Finset.filter (fun r => Odd r ∧ (fun j => Nat.factorization (3 * syracuseStep^[j.val] r + 1) 2) = ā) (Finset.range (2 ^ m))).card
          ≠ 2 ^ (m - Finset.sum Finset.univ (fun j => ā j)) :=
  solution
