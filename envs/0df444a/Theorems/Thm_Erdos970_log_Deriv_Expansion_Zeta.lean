-- Prove2me | Theorems.Thm_Erdos970_log_Deriv_Expansion_Zeta
-- name    : Erdos970.log_Deriv_Expansion_Zeta
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:15.611262+00:00
-- url     : https://prove2.me/theorems/52da49c2-2667-467c-a6ba-94c827d55d0b
-- title:
--   The logarithmic derivative of ζ near 3/2 + it, as a sum over nearby zeros plus a bounded error
-- statement:
--   Let $t$ be real with $|t|>2$ and put $c=\tfrac32+it$. Let $0<r_1<r<R_1<R<1$. Let $B>1$ be such that $|\zeta(z)|<B$ for every $z$ in the closed disc $|z-c|\le R$, and suppose the set $Z$ of zeros of $\zeta$ in the closed disc $|z-c|\le R_1$ (`zerosetKfRc R₁ c ζ`) is finite. Then for every $z$ with $|z-c|\le r_1$ and $z\notin Z$,
--
--   $$\Big|\frac{\zeta'}{\zeta}(z)-\sum_{\rho\in Z}\frac{m_\rho}{z-\rho}\Big|\le\Big(\frac{16r^2}{(r-r_1)^3}+\frac{1}{(R^2/R_1-R_1)\log(R/R_1)}\Big)\log\frac{B}{|\zeta(c)|},$$
--
--   where $m_\rho$ is the order of vanishing of $\zeta$ at $\rho$ and $\frac{\zeta'}{\zeta}$ is `logDerivZeta`, the quotient of the complex derivative of Mathlib's `riemannZeta` by `riemannZeta` (with the convention $x/0=0$).
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `Erdos970.log_Deriv_Expansion_Zeta`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace Erdos970

open scoped BigOperators
open scoped Topology
open _root_.Real
open _root_.Set
open _root_.Filter
open Topology
open _root_.MeasureTheory
open scoped BigOperators
open scoped Topology
open Metric
open _root_.Set
open _root_.Filter
open Asymptotics
open BigOperators
local notation "ι" => fun (z : ℂˣ) ↦ (z : ℂ)

theorem log_Deriv_Expansion_Zeta (t : ℝ) (ht : |t| > 2)
    (r1 r R1 R : ℝ)
    (hr1_pos : 0 < r1) (hr1_lt_r : r1 < r)
    (_hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1) :
    let c := (3/2 : ℂ) + I * t
    ∀ B > 1, (∀ z ∈ closedBall c R, ‖riemannZeta z‖ < B) →
    ∀ (hfin : (zerosetKfRc R1 c riemannZeta).Finite),
    ∀ z ∈ closedBall c r1 \ zerosetKfRc R1 c riemannZeta,
    ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖ ≤ (16 * r^2 / ((r - r1)^3) +
    1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log (B / ‖riemannZeta c‖) := by
  sorry

end Erdos970
