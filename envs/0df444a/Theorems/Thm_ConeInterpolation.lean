-- Prove2me | Theorems.Thm_ConeInterpolation
-- name    : ConeInterpolation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:51:37.520058+00:00
-- url     : https://prove2.me/theorems/a1112cfb-08ed-5fef-984a-6f3403e02940
-- title:
--   Cone Interpolation: Cone Interpolation
-- statement:
--   The truncated cone functions of paper Lemma A.1 (paper.tex 1634--1640 and 1668--1691). For any
--   finitely many (not necessarily distinct) points `e j` of a metric space `E`, any real coefficients
--   `c j`, any `M ≥ 0` and any `C ≥ 0`, the function `g x = τ_M (max_j (c j - C * d(x, e j)))` is
--   `C`-Lipschitz and bounded by `M`; and when the coefficients are *compatible* with `C`
--   (`|c j - c j'| ≤ C * d(e j, e j')`) and bounded by `M`, `g` interpolates them: `g (e j) = c j` for
--   every `j`. This is the finite McShane--Whitney Lipschitz extension.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ConeInterpolation.lean#L12-L74
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ConeInterpolation.lean#L12-L74

import Definitions.Def_Tablet_Preamble
import Definitions.Def_Tablet_ConeInterpolation
set_option autoImplicit false
open scoped NNReal

theorem ConeInterpolation {E : Type*} [MetricSpace E] {l : ℕ}
    (e : Fin (l + 1) → E) (c : Fin (l + 1) → ℝ) (M : ℝ) (C : ℝ≥0) (hM : 0 ≤ M)
    (g : E → ℝ)
    (hg : ∀ x, g x = max (-M) (min M (Finset.univ.sup' Finset.univ_nonempty
            (fun j => c j - (C : ℝ) * dist x (e j))))) :
    LipschitzWith C g ∧ (∀ x, |g x| ≤ M) ∧
      ((∀ j j', |c j - c j'| ≤ (C : ℝ) * dist (e j) (e j')) → (∀ j, |c j| ≤ M) →
        ∀ j, g (e j) = c j) := by sorry
