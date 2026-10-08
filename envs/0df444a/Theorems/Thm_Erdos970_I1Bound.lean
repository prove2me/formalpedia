-- Prove2me | Theorems.Thm_Erdos970_I1Bound
-- name    : Erdos970.I1Bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:52.054686+00:00
-- url     : https://prove2.me/theorems/75e47347-5018-477d-af42-a87fa9be1576
-- title:
--   Smoothed Chebyshev contour — the bound C·X·log X/(εT) for the first horizontal-tail integral I₁
-- statement:
--   Let $F:\mathbb R\to\mathbb R$ be a smoothing function that is $C^1$, supported in $[1/2,2]$, nonnegative on $(0,\infty)$, and of unit mass $\int_0^\infty F(x)\,dx/x=1$. Then there is a constant $C>0$ such that for all real $\varepsilon\in(0,1)$, all $X>3$ and all $T>3$,
--
--   $$\big\|I_1(F,\varepsilon,X,T)\big\|\le \frac{C\,X\log X}{\varepsilon\,T}.$$
--
--   Here $I_1$ (`I₁` in the definitions bundle) is $\frac{1}{2\pi i}\cdot i\int_{-\infty}^{-T}G(1+1/\log X+it)\,dt$ with $G(s)=-\frac{\zeta'}{\zeta}(s)\,\mathcal M(\widetilde F_\varepsilon)(s)\,X^s$, where $\mathcal M$ is the Mellin transform and $\widetilde F_\varepsilon$ (`Smooth1 F ε`) is the Mellin convolution of the indicator of $(0,1]$ with the spike $x\mapsto F(x^{1/\varepsilon})/\varepsilon$; that is, the part of the vertical line $\operatorname{Re}s=1+1/\log X$ below height $-T$. The constant $C$ depends only on $F$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `Erdos970.I1Bound`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace Erdos970

open _root_.Set
open _root_.Function
open _root_.Filter
open _root_.Complex
open _root_.Real
open _root_.ArithmeticFunction (vonMangoldt)
open ComplexConjugate
open _root_.MeasureTheory
local notation (name := mellintransform2) "𝓜" => MellinTransform
local notation "Λ" => vonMangoldt
local notation "ζ" => riemannZeta
local notation "ζ'" => deriv ζ
local notation "I" => Complex.I
local notation "ψ" => ChebyshevPsi

theorem I1Bound
    {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2) (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀(ε : ℝ) (_ : 0 < ε)
    (_ : ε < 1)
    (X : ℝ) (_ : 3 < X)
    {T : ℝ} (_ : 3 < T),
    ‖I₁ SmoothingF ε X T‖ ≤ C * X * Real.log X / (ε * T) := by
  sorry

end Erdos970
