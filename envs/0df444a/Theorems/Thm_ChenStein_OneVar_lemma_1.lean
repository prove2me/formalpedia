-- Prove2me | Theorems.Thm_ChenStein_OneVar_lemma_1
-- name    : ChenStein.OneVar.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:31:29.579136+00:00
-- url     : https://prove2.me/theorems/4e02ff1e-c4f0-46dc-8769-53077a261424
-- title:
--   Lemma 1, p. 20 — Stein solution bounds
-- statement:
--   Let $Z$ be Poisson with positive mean $\lambda$, let $0\le h(w)\le1$ for every nonnegative integer $w$, and set $f=S(h-Eh(Z))$. Then
--
--   $$\|\Delta f\|\le\frac{1-e^{-\lambda}}{\lambda},\qquad
--   \|f\|\le\min\{1,1.4\lambda^{-1/2}\}.$$
--
--   The bounds retain the paper's constants and supply the estimates used with display (11). Both sup norms range over $w\ge0$, including zero.
--
--   **Formalization Note** The supremum bounds are written pointwise to avoid a default value for an unbounded real supremum. The source fixes $f(0)=0$.
-- source:
--   Arratia, Goldstein and Gordon, Two moments suffice for Poisson approximations: the Chen-Stein method, Ann. Probab. 17 (1989), §4, p. 20, Lemma 1, first two clauses; https://doi.org/10.1214/aop/1176991491

import Mathlib
import Definitions.Def_ChenStein_OneVar_Setting

namespace ChenStein.OneVar

open scoped NNReal

/-- Arratia--Goldstein--Gordon (1989), §4, p. 20, Lemma 1. -/
theorem lemma_1 (lam : ℝ≥0) (hlam : 0 < lam) (h : ℕ → ℝ)
    (hh : ∀ w, 0 ≤ h w ∧ h w ≤ 1) :
    (∀ w, |Δ (S lam (fun k => h k - poissonMean lam h)) w| ≤
      (1 - Real.exp (-(lam : ℝ))) / (lam : ℝ)) ∧
    (∀ w, |S lam (fun k => h k - poissonMean lam h) w| ≤
      min 1 (1.4 * (lam : ℝ) ^ (-(1/2 : ℝ)))) := by sorry

end ChenStein.OneVar
