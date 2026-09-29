-- Prove2me | solution 1 for mme_subrankCapacityPoly_witness
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-31T19:46:26.447502+00:00
-- url     : https://prove2.me/submissions/4724d2d6-045c-4528-bf37-d8678575b9b6

import Definitions.Def_mme_subrank_capacity_poly

open MME BigOperators Filter

universe u

/-- **Witness-extraction from polynomial-subrank-capacity.**

For any tensor `T : TensorObj K 3` with `1 < V ≤ subrankCapacityPoly T` and
any `δ > 0`, there is a `V' > V - δ` for which the polynomial-bounded
witness family is achievable.

This is the canonical `sSup`-approximation step needed to convert the
abstract inequality `V ≤ subrankCapacityPoly T` into an actual witness
sequence usable by Hölder + asymptotic limit
(`mme_holder_subexp_capacity_omega_bound`).

**Proof outline.** Apply `Real.lt_csSup_iff_of_pos` (or analogous `sSup`
approximation) to `V - δ < sSup S`, where `S` is the set defining
`subrankCapacityPoly T`. This gives `V' ∈ S` with `V - δ < V'`; the
membership `V' ∈ S` unfolds to the polynomial-bounded witness family.

**Reusability.** Standard `sSup`-approximation pattern. Abstract;
reusable for any `subrankCapacityPoly`-style asymptotic-value functional. -/
theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} {V δ : ℝ}
    (hV : 1 < V) (h : V ≤ subrankCapacityPoly T) (hδ : 0 < δ) :
    ∃ V' : ℝ, V - δ < V' ∧ 1 ≤ V' ∧ ∃ c : ℝ,
      ∀ ε > (0 : ℝ), ∃ᶠ (N : ℕ) in atTop,
        ∃ (k : ℕ) (a b c' : Fin k → ℕ),
          (k : ℝ) ≤ ((N : ℝ) + 1) ^ c ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c' i)))
            (T.kronPow N)
          ∧ V' ^ N * (1 - ε) ≤
              ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := by
  -- The defining set of `subrankCapacityPoly T`.
  set S : Set ℝ := { V : ℝ | 1 ≤ V ∧ ∃ c : ℝ,
    ∀ ε > (0 : ℝ), ∃ᶠ (N : ℕ) in atTop,
      ∃ (k : ℕ) (a b c' : Fin k → ℕ),
        (k : ℝ) ≤ ((N : ℝ) + 1) ^ c ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c' i)))
          (T.kronPow N)
        ∧ V ^ N * (1 - ε) ≤ ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) } with hSdef
  -- By definition `subrankCapacityPoly T = sSup S`.
  have hSup : subrankCapacityPoly T = sSup S := rfl
  have hVsup : V ≤ sSup S := by rw [hSup] at h; exact h
  -- `S` is nonempty: otherwise `sSup S = sSup ∅ = 0`, contradicting `1 < V ≤ sSup S`.
  have hSne : S.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Real.sSup_empty] at hVsup
    linarith
  -- `V - δ < V ≤ sSup S`, so `V - δ < sSup S`.
  have hVδ : V - δ < sSup S := by linarith
  -- Apply sSup-approximation: get V' ∈ S with V - δ < V'.
  obtain ⟨V', hV'mem, hV'gt⟩ := exists_lt_of_lt_csSup hSne hVδ
  -- Unpack membership in S.
  rcases hV'mem with ⟨hV'one, c, hc⟩
  refine ⟨V', hV'gt, hV'one, c, hc⟩
