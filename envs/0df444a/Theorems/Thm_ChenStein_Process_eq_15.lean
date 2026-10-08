-- Prove2me | Theorems.Thm_ChenStein_Process_eq_15
-- name    : ChenStein.Process.eq_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T03:33:00.83746+00:00
-- url     : https://prove2.me/theorems/cf7d9264-05d0-471a-a932-8ee18bec6677
-- title:
--   (15), §6, p. 24 — E{(X_α − p_α)(f(U + X_βe_k) − f(U))} ≤ 2‖f‖(p_{αβ} + p_αp_β)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $(X_\alpha)_{\alpha\in I}$ a family of $\{0,1\}$-valued random variables with $p_\alpha=P(X_\alpha=1)$ and $p_{\alpha\beta}=E(X_\alpha X_\beta)$. Fix indices $\alpha,\beta$, a coordinate $k\in\{1,\dots,d\}$, any random element $U$ of $\mathbb Z_+^d$, and a function $f:\mathbb Z_+^d\to\mathbb R$ with $|f(j)|\le F$ for all $j$. Then
--   $$E\bigl\{(X_\alpha-p_\alpha)\bigl(f(U+X_\beta e_k)-f(U)\bigr)\bigr\}\le 2F\,(p_{\alpha\beta}+p_\alpha p_\beta).$$
--
--   This bounds each summand of the telescoping sum that controls the second sum of (14) in the proof of Theorem 2, and it is where the factor $2$ in front of $b_1+b_2$ comes from.
--
--   **Formalization Note** $U$ is an arbitrary measurable random element of $\mathbb Z_+^d$; no relation between $U$ and the $X$'s is assumed (in the proof it is a partial block-sum vector). $\|f_1\|$ of the page is the bound $F$. The index $\beta$ may equal $\alpha$.
-- source:
--   Arratia, Goldstein and Gordon, Two moments suffice for Poisson approximations: the Chen-Stein method, Ann. Probab. 17 (1989), p. 24, §6, display (15)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_ChenStein_Process_Setting

namespace ChenStein.Process

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem eq_15
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {I : Type*} (X : I → Ω → ℕ) (hXm : ∀ α, Measurable (X α)) (hX01 : ∀ α ω, X α ω ≤ 1)
    (α β : I) {d : ℕ} (k : Fin d) (U : Ω → (Fin d → ℕ)) (hU : Measurable U)
    (f : (Fin d → ℕ) → ℝ) (F : ℝ) (hF : ∀ j, |f j| ≤ F) :
    ∫ ω, ((X α ω : ℝ) - p P X α) * (f (U ω + X β ω • e k) - f (U ω)) ∂P
      ≤ 2 * F * (pab P X α β + p P X α * p P X β) := by sorry

end ChenStein.Process
