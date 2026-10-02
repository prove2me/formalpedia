-- Prove2me | Theorems.Thm_Disjunctive_SimplexTableau_tableau_coefficient_formulas
-- name    : Disjunctive.SimplexTableau.tableau_coefficient_formulas
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T16:51:54.153634+00:00
-- url     : https://prove2.me/theorems/20b5ff8a-2a16-4152-ac1c-3f2186c2ebb6
-- title:
--   Lemma 9.1 — the tableau-coefficient formulas
-- statement:
--   This is Lemma 9.1 of Balas's *Disjunctive Programming*: the simplex tableau
--   coefficients of eq. (9.1), for the basic solution with nonbasic set `J`, satisfy
--   `ā_ij=-(Ã_iÂ⁻¹)_j` (9.4) and `ā_i0=Ã_iÂ⁻¹b̂-b̃_i` (9.5), for every row `i=1,…,m+p+n`.
--
--   The book's proof writes out the basis matrix `E` for `(LP)` and its inverse in block form (using
--   the four cases `i∈B` or `P`, `j∈R` or `Q`, for structural vs. surplus basic/nonbasic variables),
--   verifying the closed form in each case; it cites [33] for the detailed case verification.
--
--   **Formalization Note.** Stated as the identity `SurplusM i x = Abar0Row i - Σ AbarRow i l *
--   SurplusM (ι l) x`, true for every `x` (given `Â` nonsingular) since `s_i:=Ã_ix-b̃_i` and
--   `x=Â⁻¹b̂+Â⁻¹s_J` (eq. (8.4), from `Âx=b̂+s_J`'s own definition) combine tautologically into exactly
--   this formula — avoiding the book's own four-case block-matrix bookkeeping (`B,R,P,Q`), which is
--   proof machinery for *how* to derive the closed form, not part of what the closed form asserts.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 108, Lemma 9.1

import Mathlib
import Definitions.Def_Disjunctive_SimplexTableau_Tableau

namespace Disjunctive.SimplexTableau

/-- Lemma 9.1 (Balas §9.1, p. 108-109): the simplex tableau coefficients `ā_ij`, `ā_i0`
(eq. (9.4)-(9.5)) correctly express, for *every* row `i` of `Ã`, its slack value as an affine
function of the nonbasic rows' (indexed by `J`, enumerated by `ι`) slack values, for every `x`. -/
theorem tableau_coefficient_formulas {n : ℕ} {M : Type*} [Fintype M] [DecidableEq (Fin n)]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (ι : Fin n → M) (hι_inj : Function.Injective ι)
    (hnonsing : IsUnit (Ahat Atil ι).det) (i : M) (x : Fin n → ℝ) :
    SurplusM Atil btil i x =
      Abar0Row Atil btil ι i - ∑ l, AbarRow Atil ι i l * SurplusM Atil btil (ι l) x := by sorry

end Disjunctive.SimplexTableau
