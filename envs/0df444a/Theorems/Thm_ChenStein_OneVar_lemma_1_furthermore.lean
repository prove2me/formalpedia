-- Prove2me | Theorems.Thm_ChenStein_OneVar_lemma_1_furthermore
-- name    : ChenStein.OneVar.lemma_1_furthermore
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T03:31:44.625653+00:00
-- url     : https://prove2.me/theorems/1b5f4940-3e82-4e73-a84f-4c19014a5515
-- title:
--   Lemma 1, p. 21 — sharp special-case sup norm
-- statement:
--   For a Poisson law of positive mean $\lambda$, set $h(w)=\mathbf1_{\{0\}}(w)-e^{-\lambda}$ and $f=Sh$. Then
--
--   $$\|f\|=\frac{1-e^{-\lambda}}{\lambda}.$$
--
--   This is the final clause of Lemma 1, establishing attainment of the first constant in a special case.
--
--   **Formalization Note** Equality of a supremum is encoded as a bound at every $w$ together with existence of a $w$ attaining it. The chosen $h$ has Poisson mean zero.
-- source:
--   Arratia, Goldstein and Gordon, Two moments suffice for Poisson approximations: the Chen-Stein method, Ann. Probab. 17 (1989), §4, p. 21, final clause of Lemma 1; https://doi.org/10.1214/aop/1176991491

import Mathlib
import Definitions.Def_ChenStein_OneVar_Setting

namespace ChenStein.OneVar

open scoped NNReal

/-- Arratia--Goldstein--Gordon (1989), §4, p. 21, last clause of Lemma 1. -/
theorem lemma_1_furthermore (lam : ℝ≥0) (hlam : 0 < lam) :
    (∀ w, |S lam (fun k => (if k = 0 then 1 else 0) - Real.exp (-(lam : ℝ))) w| ≤
      (1 - Real.exp (-(lam : ℝ))) / (lam : ℝ)) ∧
    (∃ w, |S lam (fun k => (if k = 0 then 1 else 0) - Real.exp (-(lam : ℝ))) w| =
      (1 - Real.exp (-(lam : ℝ))) / (lam : ℝ)) := by sorry

end ChenStein.OneVar
