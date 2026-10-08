-- Prove2me | Theorems.Thm_Erdos970_SmoothedChebyshevPull1
-- name    : Erdos970.SmoothedChebyshevPull1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:28.67966+00:00
-- url     : https://prove2.me/theorems/ea208025-4280-4117-8a32-c11dd5c9516e
-- title:
--   Shifting the contour — the smoothed Chebyshev function as I₁ − I₂ + I₃₇ + I₈ + I₉ plus the residue at s = 1
-- statement:
--   Let $0<\varepsilon<1$, $X>3$, $T>0$ and $0<\sigma_1<1$. Suppose $\zeta'/\zeta$ is holomorphic on $\{\sigma+i\tau:\sigma_1\le\sigma\le2,\ -T\le\tau\le T\}\setminus\{1\}$. Let $F:\mathbb R\to\mathbb R$ be $C^1$, supported in $[1/2,2]$, nonnegative on $(0,\infty)$, with $\int_0^\infty F(x)\,dx/x=1$. Then
--
--   $$\psi_\varepsilon(X)=I_1-I_2+I_{37}+I_8+I_9+\mathcal M(\widetilde F_\varepsilon)(1)\,X,$$
--
--   where $\psi_\varepsilon(X)$ is `SmoothedChebyshev F ε X`, $\widetilde F_\varepsilon$ is `Smooth1 F ε`, $\mathcal M$ is the Mellin transform, and $I_1=I_1(F,\varepsilon,X,T)$, $I_2=I_2(F,\varepsilon,T,X,\sigma_1)$, $I_{37}=I_{37}(F,\varepsilon,T,X,\sigma_1)$, $I_8=I_8(F,\varepsilon,T,X,\sigma_1)$, $I_9=I_9(F,\varepsilon,X,T)$ are the bundle's integrals of $G(s)=-\frac{\zeta'}{\zeta}(s)\mathcal M(\widetilde F_\varepsilon)(s)X^s$, each multiplied by $1/(2\pi i)$, over the pieces of the shifted contour: $I_1$ and $I_9$ over $\operatorname{Re}s=1+1/\log X$ with $\operatorname{Im}s\le-T$ and $\operatorname{Im}s\ge T$ (as $i\int dt$), $I_2$ and $I_8$ over the horizontal segments $\sigma\mp iT$, $\sigma_1\le\sigma\le1+1/\log X$, and $I_{37}$ over the vertical segment $\sigma_1+it$, $|t|\le T$ (as $i\int dt$). The left side $\psi_\varepsilon(X)$ is the integral of $G/(2\pi i)$ over the whole line $\operatorname{Re}s=1+1/\log X$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `Erdos970.SmoothedChebyshevPull1`

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

theorem SmoothedChebyshevPull1 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos: 0 < ε)
    (ε_lt_one : ε < 1)
    (X : ℝ) (X_gt : 3 < X)
    {T : ℝ} (T_pos : 0 < T) {σ₁ : ℝ}
    (σ₁_pos : 0 < σ₁) (σ₁_lt_one : σ₁ < 1)
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ₁ 2)×ℂ (Icc (-T) T) \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    SmoothedChebyshev SmoothingF ε X =
      I₁ SmoothingF ε X T -
      I₂ SmoothingF ε T X σ₁ +
      I₃₇ SmoothingF ε T X σ₁ +
      I₈ SmoothingF ε T X σ₁ +
      I₉ SmoothingF ε X T
      + 𝓜 ((Smooth1 SmoothingF ε) ·) 1 * X := by
  sorry

end Erdos970
