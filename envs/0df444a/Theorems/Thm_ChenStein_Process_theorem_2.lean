-- Prove2me | Theorems.Thm_ChenStein_Process_theorem_2
-- name    : ChenStein.Process.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:33:19.665978+00:00
-- url     : https://prove2.me/theorems/aa879d51-5742-4bf0-88ab-f0bec81850a9
-- title:
--   Theorem 2, p. 11 — a dependent Bernoulli process X satisfies ‖𝓛(X) − 𝓛(Y)‖ ≤ 2(2b₁ + 2b₂ + b₃) for the Poisson process Y with intensity p_(·)
-- statement:
--   Let $I$ be an index set and $(X_\alpha)_{\alpha\in I}$ Bernoulli random variables on a probability space, with $p_\alpha=P(X_\alpha=1)>0$ and
--   $$\lambda=\sum_{\alpha\in I}p_\alpha\in(0,\infty).$$
--   For each $\alpha$ choose $B_\alpha\subseteq I$ with $\alpha\in B_\alpha$, and let
--   $$b_1=\sum_{\alpha\in I}\sum_{\beta\in B_\alpha}p_\alpha p_\beta,\qquad b_2=\sum_{\alpha\in I}\sum_{\alpha\ne\beta\in B_\alpha}E(X_\alpha X_\beta),\qquad b_3=\sum_{\alpha\in I}E\bigl|E\{X_\alpha-p_\alpha\mid\sigma(X_\beta:\beta\in I-B_\alpha)\}\bigr|.$$
--   For $\alpha\in I$ let $Y_\alpha$ be Poisson with mean $p_\alpha$, the $Y_\alpha$ mutually independent. Then the dependent Bernoulli process $\mathbf X=(X_\alpha)_{\alpha\in I}$ and the Poisson process $\mathbf Y=(Y_\alpha)_{\alpha\in I}$ on $I$ with intensity $p_{(\cdot)}$ satisfy
--   $$\|\mathcal L(\mathbf X)-\mathcal L(\mathbf Y)\|\le2(2b_1+2b_2+b_3),$$
--   where $\|\mathcal L(\mathbf X)-\mathcal L(\mathbf Y)\|=2\sup_A|P(\mathbf X\in A)-P(\mathbf Y\in A)|$ is the paper's total variation norm (twice the usual distance).
--
--   When $b_1,b_2,b_3$ are small, the locations of the dependent events are approximately a Poisson process; the bound needs only the first two moments $p_\alpha$, $p_{\alpha\beta}$ when $X_\alpha$ is independent of the variables outside $B_\alpha$ ($b_3=0$).
--
--   **Formalization Note** The laws are the image measures of $\omega\mapsto(X_\alpha(\omega))_\alpha$ and $\omega'\mapsto(Y_\alpha(\omega'))_\alpha$ on $\mathbb N^I$ with the product σ-algebra; $\mathbf Y$ lives on its own probability space, since total variation compares only laws. Mutual independence of the $Y_\alpha$ is a hypothesis (`iIndepFun`). The norm is `2 * tvDist`, with `tvDist` the supremum over measurable sets of $|\mu(A)-\nu(A)|$. $b_1,b_2,b_3$ are $[0,\infty]$-valued and the inequality is read in $[0,\infty]$ (an infinite $b$ makes the bound vacuous, as on the page). The index set is assumed countable, which loses nothing ($p_\alpha>0$ and $\sum p_\alpha<\infty$ force it) and makes the process measurable. The Bernoulli variables are $\mathbb N$-valued and bounded by $1$.
-- source:
--   Arratia, Goldstein and Gordon, Two moments suffice for Poisson approximations: the Chen-Stein method, Ann. Probab. 17 (1989), p. 11, Theorem 2; setting of §2, p. 10

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_ChenStein_Process_Setting

namespace ChenStein.Process

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem theorem_2
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {I : Type*} [Countable I]
    (X : I → Ω → ℕ) (hXm : ∀ α, Measurable (X α)) (hX01 : ∀ α ω, X α ω ≤ 1)
    (hp : ∀ α, 0 < p P X α)
    (lam : ℝ) (hlam : HasSum (p P X) lam) (hlam0 : 0 < lam)
    (B : I → Set I) (hB : ∀ α, α ∈ B α)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : I → Ω' → ℕ) (hYm : ∀ α, Measurable (Y α)) (hYind : iIndepFun Y P')
    (hYlaw : ∀ α, P'.map (Y α) = poissonMeasure (p P X α).toNNReal) :
    ENNReal.ofReal (2 * MarkovChainCLT.tvDist (P.map (Xproc X)) (P'.map (Xproc Y)))
      ≤ 2 * (2 * b1 P X B + 2 * b2 P X B + b3 P X B) := by sorry

end ChenStein.Process
