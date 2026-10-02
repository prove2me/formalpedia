-- Prove2me | Theorems.Thm_Disjunctive_CutCorrespondence_strengthened_cut_correspondence
-- name    : Disjunctive.CutCorrespondence.strengthened_cut_correspondence
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T16:48:44.294299+00:00
-- url     : https://prove2.me/theorems/80adfdcb-bdda-4647-b721-1a53232dddc8
-- title:
--   Theorem 8.5 — the correspondence extends to strengthened cuts
-- statement:
--   This is Theorem 8.5 of Balas's *Disjunctive Programming*: Theorems 8.4A/8.4B remain
--   valid after strengthening both cuts — `αx≥β` becomes the strengthened lift-and-project cut `γx≥β`
--   of Theorem 6.4, and `π^s_Jx_J≥π0` becomes the mixed integer Gomory cut `π̄^s_Jx_J≥π0` of eq.
--   (8.10).
--
--   The book's proof outline: the only coefficients of `π^s_J≥π0` that can possibly be strengthened
--   are those `π_j` with `j∈J∩N'` (structural integer-constrained nonbasic variables); citing [32], it
--   states that these are exactly the coefficients of `αx≥β` that can be strengthened, and the
--   resulting `γ_j` equal the `π̄_j`.
--
--   **Formalization Note.** Uses the same basic-solution hypotheses as Theorem 8.4A (continuing its
--   setup, as the book's own "remain valid" phrasing indicates), with `α` replaced by `Gamma` on the
--   left and `PiCoef` replaced by `PiBar` (via `StrengthenedSimpleDisjCutSet`) on the right; `β` is
--   unchanged, matching Theorem 6.4's own `γx≥β` (same `β`).
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 103, Theorem 8.5

import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau

namespace Disjunctive.CutCorrespondence

/-- Theorem 8.5 (Balas §8.2, p. 103): Theorems 8.4A/8.4B remain valid if `αx ≥ β` is replaced by
the strengthened lift-and-project cut `γx ≥ β` (Theorem 6.4) and `π^s_J x_J ≥ π0` is replaced by
the mixed integer Gomory cut `π̄^s_J x_J ≥ π0` (eq. (8.10)), for the 0-1 row-position set
`Nprime` (see `MODERATION_NOTES.md`). The solution is **basic**, not merely feasible with the given supports: support containment alone is false (one row `x ≥ 1/2` in `n = 1` with `u = 0.3`, `v = 0.1`, `u₀ = v₀ = 0.1` satisfies the hypotheses, `M1`/`M2` are not disjoint and Theorem 8.4A yields `x ≥ 3/4` instead of `x ≥ 1`). -/
theorem strengthened_cut_correspondence {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (M1 M2 : Finset M)
    (ι : Fin n → M) (Nprime : Finset (Fin n))
    (hbasic : IsBasicCGLPKSolution Atil btil k α u u0 v v0 β) (hu0 : 0 < u0) (hv0 : 0 < v0)
    (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0)
    (hι_inj : Function.Injective ι) (hι_image : Finset.image ι Finset.univ = M1 ∪ M2)
    (hnonsing : IsUnit (Ahat Atil ι).det) :
    {x | β ≤ dotProduct (Gamma Atil u u0 v v0 k Nprime α) x} =
      StrengthenedSimpleDisjCutSet Atil btil ι k Nprime := by sorry

end Disjunctive.CutCorrespondence
