-- Prove2me | Theorems.Thm_Erdos970_SmoothedChebyshevClose
-- name    : Erdos970.SmoothedChebyshevClose
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:00.132998+00:00
-- url     : https://prove2.me/theorems/70800b4c-f158-4e38-927e-d0a6639ab14c
-- title:
--   The smoothed Chebyshev function is within C·ε·X·log X of ψ(X)
-- statement:
--   Let $F:\mathbb R\to\mathbb R$ be $C^1$, supported in $[1/2,2]$, nonnegative on $(0,\infty)$, with $\int_0^\infty F(x)\,dx/x=1$. Then there is $C>0$ such that for all $X>3$ and $\varepsilon\in(0,1)$ with $X\varepsilon>2$,
--
--   $$\big|\psi_{\varepsilon}(X)-\psi(X)\big|\le C\,\varepsilon\,X\log X,$$
--
--   where $\psi(X)$ is the Chebyshev function `ChebyshevPsi X` of the bundle and $\psi_\varepsilon(X)$ is the smoothed Chebyshev function `SmoothedChebyshev F ε X`, defined in the bundle as the vertical integral $\frac{1}{2\pi i}\int_{\operatorname{Re}s=1+1/\log X}-\frac{\zeta'}{\zeta}(s)\,\mathcal M(\widetilde F_\varepsilon)(s)\,X^s\,ds$. Here $\widetilde F_\varepsilon$ (`Smooth1 F ε`) is the Mellin convolution of the indicator of $(0,1]$ with the spike $x\mapsto F(x^{1/\varepsilon})/\varepsilon$, and $\mathcal M$ is the Mellin transform.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `Erdos970.SmoothedChebyshevClose`

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

theorem SmoothedChebyshevClose {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1) :
    ∃ C > 0, ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε),
    ‖SmoothedChebyshev SmoothingF ε X - ChebyshevPsi X‖ ≤ C * ε * X * Real.log X := by
  sorry

end Erdos970
