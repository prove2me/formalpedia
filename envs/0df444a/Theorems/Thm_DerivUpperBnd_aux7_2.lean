-- Prove2me | Theorems.Thm_DerivUpperBnd_aux7_2
-- name    : DerivUpperBnd_aux7_2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:17:04.877406+00:00
-- url     : https://prove2.me/theorems/a643a4e6-1f72-4372-978b-10cb5b8c2d3f
-- title:
--   Sawtooth factor is dominated by $1$: $|\lfloor x\rfloor + \tfrac12 - x|\, x^{-\sigma-1} \log x \le x^{-\sigma-1} \log x$
-- statement:
--   Let $x \ge 1$ and $\sigma$ be real. Then
--   $$\Big| \lfloor x \rfloor + \tfrac{1}{2} - x \Big| \; x^{-\sigma-1}\, \log x \;\le\; x^{-\sigma-1}\, \log x.$$
--
--   The centered sawtooth $\lfloor x \rfloor + \tfrac12 - x$ always lies in $[-\tfrac12, \tfrac12]$, so its absolute value is at most $\tfrac12 \le 1$; since $x^{-\sigma-1} \ge 0$ and $\log x \ge 0$ for $x \ge 1$, multiplying by the remaining nonnegative factors preserves the inequality.
--
--   This is the pointwise domination step in the tail estimate for the differentiated Euler–Maclaurin representation of $\zeta$: after the modulus identity reduces the complex integrand to this real expression, dropping the sawtooth factor leaves the explicitly integrable function $x^{-\sigma-1}\log x$ on $(N, \infty)$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1583-L1587

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

theorem DerivUpperBnd_aux7_2 {x σ : ℝ} (hx : 1 ≤ x) :
    |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log ≤ x ^ (-σ - 1) * x.log := by sorry
