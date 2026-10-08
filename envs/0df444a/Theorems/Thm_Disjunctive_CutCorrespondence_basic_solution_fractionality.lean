-- Prove2me | Theorems.Thm_Disjunctive_CutCorrespondence_basic_solution_fractionality
-- name    : Disjunctive.CutCorrespondence.basic_solution_fractionality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:47:27.249392+00:00
-- url     : https://prove2.me/theorems/af5b7c19-db37-48c3-929c-1bd28522b6a5
-- title:
--   Lemma 8.3 — the resulting x_k is strictly fractional
-- statement:
--   This is Lemma 8.3 of Balas's *Disjunctive Programming* — **not extracted by
--   `statements.jsonl`'s regex pass**; verified directly against the PDF and added manually, per
--   `BRIEF.md`'s explicit flag that it "sits between Lemma 8.2 and Theorem 8.4A."
--
--   Continuing Lemma 8.2's basic solution, `0 < ā_k0 < 1`. The book's proof: from (8.3),
--   `(uM1,-vM2) = (u0+v0)e_kÂ⁻¹`, so `(u0+v0)e_kÂ⁻¹b̂ = v0`, and since `u0,v0>0`,
--   `0 < ā_k0 = e_kÂ⁻¹b̂ = v0/(u0+v0) < 1`.
--
--   **Formalization Note.** Restates Lemma 8.2's exact hypotheses (basic solution with `u0,v0>0`,
--   basic components indexed by `M1,M2`, nonsingular `Â` enumerated by `ι`) rather than re-deriving
--   them, since Lemma 8.3 explicitly continues from Lemma 8.2's own setup.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 100, Lemma 8.3

import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau

namespace Disjunctive.CutCorrespondence

/-- Lemma 8.3 (Balas §8.1, p. 100): continuing Lemma 8.2's basic solution (with basic
`u`/`v`-components indexed by `M1`/`M2`) and its associated nonsingular submatrix `Â`
(enumerated by `ι`, with `M1 ∪ M2` the image of `ι`), the resulting value of `x_k` is strictly
between `0` and `1`: `0 < ā_k0 < 1`. The solution is **basic**, not merely feasible with the given supports: support containment alone is false (one row `x ≥ 1/2` in `n = 1` with `u = 0.3`, `v = 0.1`, `u₀ = v₀ = 0.1` satisfies the hypotheses, `M1`/`M2` are not disjoint and Theorem 8.4A yields `x ≥ 3/4` instead of `x ≥ 1`). -/
theorem basic_solution_fractionality {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (M1 M2 : Finset M)
    (ι : Fin n → M) (hbasic : IsBasicCGLPKSolution Atil btil k α u u0 v v0 β) (hu0 : 0 < u0)
    (hv0 : 0 < v0) (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0)
    (hι_inj : Function.Injective ι) (hι_image : Finset.image ι Finset.univ = M1 ∪ M2)
    (hnonsing : IsUnit (Ahat Atil ι).det) :
    0 < Abar0 Atil btil ι k ∧ Abar0 Atil btil ι k < 1 := by sorry

end Disjunctive.CutCorrespondence
