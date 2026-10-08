-- Prove2me | Theorems.Thm_ChanceDetEquiv_EModel_eq_19a
-- name    : ChanceDetEquiv.EModel.eq_19a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:57:01.774994+00:00
-- url     : https://prove2.me/theorems/175ebb77-e962-4881-8806-a207796505fb
-- title:
--   Eq. (19a) — for uncorrelated b and c, E(c′Db) = (Ec)′D(Eb)
-- statement:
--   Let $b$ and $c$ be random vectors in $\mathbb R^m$ and $\mathbb R^n$ on a probability space, with integrable components $b_k$, $c_j$ and integrable products $c_jb_k$. Suppose $b$ and $c$ are uncorrelated in the sense that $E(c_jb_k)=E(c_j)\,E(b_k)$ for all $j,k$ (no assumption is made on the components of $b$ among themselves, or of $c$). Then for every $n\times m$ matrix $D$,
--   $$E(c'Db)=(Ec)'D(Eb)=\mu_c'D\mu_b.$$
--
--   This is the step that makes the objective of the E-model deterministic: the expected functional of (18) becomes the bilinear function $\mu_c'D\mu_b$ of the decision rule.
--
--   **Formalization Note** The paper's "b and c are uncorrelated" is stated as the componentwise product rule for expectations, which is exactly what uncorrelatedness of the components means.
-- source:
--   Charnes and Cooper, Deterministic Equivalents for Optimizing and Satisficing under Chance Constraints, Oper. Res. 11 (1963), p. 26, Eq. (19a)

import Mathlib
import Definitions.Def_ChanceDetEquiv_EModel_Model

open MeasureTheory ProbabilityTheory Matrix

namespace ChanceDetEquiv.EModel

/-- **Eq. (19a)**, p. 26: if `b` and `c` are uncorrelated (componentwise:
`E(c_j b_k) = E(c_j) E(b_k)`), then `E(c'Db) = (Ec)'D(Eb)` for every decision rule `D`. -/
theorem eq_19a {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {m n : ℕ} (b : Ω → Fin m → ℝ) (c : Ω → Fin n → ℝ)
    (hb : ∀ k, Integrable (fun ω => b ω k) P)
    (hc : ∀ j, Integrable (fun ω => c ω j) P)
    (hcb : ∀ j k, Integrable (fun ω => c ω j * b ω k) P)
    (huncorr : ∀ j k, ∫ ω, c ω j * b ω k ∂P = (∫ ω, c ω j ∂P) * (∫ ω, b ω k ∂P))
    (D : Matrix (Fin n) (Fin m) ℝ) :
    expectedObjective P b c D = detObjective P b c D := by sorry

end ChanceDetEquiv.EModel
