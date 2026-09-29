-- Prove2me | Theorems.Thm_DerivUpperBnd_aux7_3
-- name    : DerivUpperBnd_aux7_3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:17:33.360718+00:00
-- url     : https://prove2.me/theorems/e4dd0c81-ad3c-48d3-b38c-1b49df1c4aac
-- title:
--   An explicit antiderivative of $x^{-\sigma-1}\log x$
-- statement:
--   Let $x, \sigma \in \mathbb{R}$ with $x > 0$ and $\sigma \neq 0$. Consider the function
--   $$F(t) = -\left(\frac{1}{\sigma^2}\, t^{-\sigma} + \frac{1}{\sigma}\, t^{-\sigma} \log t\right).$$
--   Then $F$ is differentiable at $x$ with
--   $$F'(x) = x^{-\sigma-1} \log x.$$
--
--   In other words, $F$ is an explicit antiderivative of $t \mapsto t^{-\sigma-1}\log t$ on the positive reals, verified in the strong sense of `HasDerivAt` at the single point $x$. Here $t^{-\sigma}$ denotes the real power function.
--
--   This is a calculus building block used in the PNT+ project to evaluate the improper integral $\int_a^\infty x^{-\sigma-1}\log x\,dx$ appearing in upper bounds for the derivative $\zeta'(s)$ of the Riemann zeta function along the Euler-Maclaurin representation. It is reusable wherever a closed-form primitive of $x^{-\sigma-1}\log x$ is needed.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1589-L1602

import Batteries.Tactic.Lemma
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/

-- Alternative cleaner proof using more direct approach

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

theorem DerivUpperBnd_aux7_3 {x σ : ℝ} (xpos : 0 < x) (σnz : σ ≠ 0) :
    HasDerivAt (fun t ↦ -(1 / σ ^ 2 * t ^ (-σ) + 1 / σ * t ^ (-σ) * Real.log t))
      (x ^ (-σ - 1) * Real.log x) x := by sorry
