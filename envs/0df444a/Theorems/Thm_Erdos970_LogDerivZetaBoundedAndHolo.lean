-- Prove2me | Theorems.Thm_Erdos970_LogDerivZetaBoundedAndHolo
-- name    : Erdos970.LogDerivZetaBoundedAndHolo
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:06.256002+00:00
-- url     : https://prove2.me/theorems/b2624b2f-5885-4116-910c-214634bf5a0f
-- title:
--   A zero-free region with a log⁹ bound for ζ′/ζ, and holomorphy of ζ′/ζ on the truncated region
-- statement:
--   There are real constants $A\in(0,1/2]$ and $C>0$ such that
--
--   1. `LogDerivZetaHasBound A C` holds: for all real $\sigma,t$ with $|t|>3$ and $\sigma\ge1-A/\log|t|$, one has $|\zeta'(\sigma+it)/\zeta(\sigma+it)|\le C(\log|t|)^9$ (the exponent in this bundle definition is $9$); and
--   2. for every $T\ge3$ the function $s\mapsto\zeta'(s)/\zeta(s)$ is holomorphic (complex differentiable at every point) on the set
--   $$\big\{s=\sigma+i\tau:\ 1-A/\log T\le\sigma\le2,\ -T\le\tau\le T\big\}\setminus\{1\}.$$
--
--   $\zeta$ is Mathlib's `riemannZeta` and $\zeta'$ its derivative.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `Erdos970.LogDerivZetaBoundedAndHolo`

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

theorem LogDerivZetaBoundedAndHolo : ∃ A C : ℝ, 0 < C ∧ A ∈ Ioc 0 (1 / 2) ∧ LogDerivZetaHasBound A C
    ∧ ∀ (T : ℝ) (_ : 3 ≤ T),
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (( (Icc ((1 : ℝ) - A / Real.log T ^ 1) 2)  ×ℂ (Icc (-T) T) ) \ {1}) := by
  sorry

end Erdos970
