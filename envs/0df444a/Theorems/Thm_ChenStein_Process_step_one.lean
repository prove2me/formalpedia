-- Prove2me | Theorems.Thm_ChenStein_Process_step_one
-- name    : ChenStein.Process.step_one
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:33:05.372244+00:00
-- url     : https://prove2.me/theorems/463d878f-18db-4d6b-b87d-1f963e15c5fc
-- title:
--   (13)–(14), §6, p. 23 — the step i = 1: |Eh(W₁,…,W_d) − Eh(Z₁,W₂,…,W_d)| ≤ 2‖f₁‖Σp_α² + 2‖f₁‖ΣΣ(p_{αβ}+p_αp_β) + ‖f₁‖Σs_α
-- statement:
--   Work in the setting of §2: $(X_\alpha)_{\alpha\in I}$ are Bernoulli random variables with $p_\alpha=P(X_\alpha=1)>0$ and $\lambda=\sum_\alpha p_\alpha\in(0,\infty)$, and for each $\alpha$ a neighbourhood $B_\alpha\ni\alpha$ is chosen. Partition $I$ into nonempty blocks $I(1),\dots,I(d)$, let $W_j=\sum_{\alpha\in I(j)}X_\alpha$ and $\lambda_j=\sum_{\alpha\in I(j)}p_\alpha$, and write $W=(W_1,\dots,W_d)$.
--
--   Fix $h:\mathbb Z_+^d\to\mathbb R$ with $\|h\|\le1$, let $f_1=S_1(h-P_1h)$ be the coordinate-1 Stein solution with parameter $\lambda_1$, and let $F$ bound $|f_1|$ everywhere. Let $Z_1$ be a Poisson random variable with mean $\lambda_1$ on the same space, independent of the process $(X_\alpha)$. Then
--   $$\bigl|E\,h(W_1,W_2,\dots,W_d)-E\,h(Z_1,W_2,\dots,W_d)\bigr|\le 2F\sum_{\alpha\in I(1)}p_\alpha^2+2F\sum_{\alpha\in I(1)}\sum_{\alpha\ne\beta\in B_\alpha}\bigl(p_{\alpha\beta}+p_\alpha p_\beta\bigr)+F\sum_{\alpha\in I(1)}s_\alpha,$$
--   with $s_\alpha=E|E\{X_\alpha-p_\alpha\mid\sigma(X_\beta:\beta\in I-B_\alpha)\}|$.
--
--   This is the first of the $d$ coordinate-replacement steps whose combination proves the finite-dimensional bound of Theorem 2; the paper writes it out in full and describes the general step in one sentence.
--
--   **Formalization Note** The sums on the right are in $[0,\infty]$. The paper's $Z_1$ is the first coordinate of the independent vector $(Z_1,\dots,Z_d)$; here only $Z_1$ is carried, with its law (Poisson with mean $\lambda_1$) and its independence from the whole process $X$ as hypotheses, which is what makes $E\,h(Z_1,W_2,\dots,W_d)=E\,(P_1h)(W)$. The page's "$2\|f_i\|$" in the middle term is a misprint for $2\|f_1\|$; the statement uses the bound $F$ on $|f_1|$ throughout. The paper's block $I(1)$ is `part⁻¹{0}` (coordinates are indexed by `Fin d`). The general step $i$ (with $Z_1,\dots,Z_{i-1}$ in front) is not stated.
-- source:
--   Arratia, Goldstein and Gordon, Two moments suffice for Poisson approximations: the Chen-Stein method, Ann. Probab. 17 (1989), p. 23, §6, displays (13)–(14)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_ChenStein_Process_Setting

namespace ChenStein.Process

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem step_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {I : Type*} [Countable I]
    (X : I → Ω → ℕ) (hXm : ∀ α, Measurable (X α)) (hX01 : ∀ α ω, X α ω ≤ 1)
    (hp : ∀ α, 0 < p P X α)
    (lam : ℝ) (hlam : HasSum (p P X) lam) (hlam0 : 0 < lam)
    (B : I → Set I) (hB : ∀ α, α ∈ B α)
    {d : ℕ} [NeZero d] (part : I → Fin d) (hpart : Function.Surjective part)
    (h : (Fin d → ℕ) → ℝ) (hh : ∀ j, |h j| ≤ 1) (F : ℝ)
    (hF : ∀ j, |Si 0 (lamj P X part 0).toNNReal
      (h - Pi_ 0 (lamj P X part 0).toNNReal h) j| ≤ F)
    (Z1 : Ω → ℕ) (hZ1m : Measurable Z1)
    (hZ1law : P.map Z1 = poissonMeasure (lamj P X part 0).toNNReal)
    (hZ1ind : IndepFun Z1 (Xproc X) P) :
    ENNReal.ofReal |∫ ω, h (Wvec X part ω) ∂P
        - ∫ ω, h (Function.update (Wvec X part ω) 0 (Z1 ω)) ∂P|
      ≤ 2 * ENNReal.ofReal F * ∑' α : {α // part α = 0}, ENNReal.ofReal (p P X α ^ 2)
        + 2 * ENNReal.ofReal F * ∑' α : {α // part α = 0},
            ∑' β : {β // β ∈ B α ∧ β ≠ α},
              ENNReal.ofReal (pab P X α β + p P X α * p P X β)
        + ENNReal.ofReal F * ∑' α : {α // part α = 0}, s P X B α := by sorry

end ChenStein.Process
