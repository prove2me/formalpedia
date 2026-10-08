-- Prove2me | Theorems.Thm_ChenStein_OneVar_telescoping_term_le
-- name    : ChenStein.OneVar.telescoping_term_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T03:31:16.421896+00:00
-- url     : https://prove2.me/theorems/7f68f260-6dd2-4a3d-83d1-f3c803cade6c
-- title:
--   §5, p. 22 — one telescoping term bound
-- statement:
--   Let $X_\alpha,X_\beta$ be Bernoulli indicators, let $U$ be any measurable nonnegative integer-valued random variable, and suppose $|\Delta f(w)|\le D$ for every $w$. With $p_\alpha=E X_\alpha$ and $p_{\alpha\beta}=E(X_\alpha X_\beta)$,
--
--   $$E[(X_\alpha-p_\alpha)(f(U+X_\beta)-f(U))]\le D(p_{\alpha\beta}+p_\alpha p_\beta).$$
--
--   This is the bound on one term of the telescoping sum on p. 22. No independence or relation between $U$ and the indicators is needed; the source uses $U$ as a partial sum.
-- source:
--   Arratia, Goldstein and Gordon, Two moments suffice for Poisson approximations: the Chen-Stein method, Ann. Probab. 17 (1989), §5, p. 22, displayed telescoping calculation; https://doi.org/10.1214/aop/1176991491

import Mathlib
import Definitions.Def_ChenStein_OneVar_Setting

namespace ChenStein.OneVar

open MeasureTheory

/-- Arratia--Goldstein--Gordon (1989), §5, p. 22: one telescoping term. -/
theorem telescoping_term_le {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : I → Ω → ℕ) (hXm : ∀ α, Measurable (X α))
    (hX01 : ∀ α ω, X α ω ≤ 1) (α β : I)
    (U : Ω → ℕ) (hUm : Measurable U) (f : ℕ → ℝ) (D : ℝ)
    (hD : ∀ w, |Δ f w| ≤ D) :
    ∫ ω, ((X α ω : ℝ) - p P X α) * (f (U ω + X β ω) - f (U ω)) ∂P
      ≤ D * (pab P X α β + p P X α * p P X β) := by sorry

end ChenStein.OneVar
