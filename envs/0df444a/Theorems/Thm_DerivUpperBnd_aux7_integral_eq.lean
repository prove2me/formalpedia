-- Prove2me | Theorems.Thm_DerivUpperBnd_aux7_integral_eq
-- name    : DerivUpperBnd_aux7_integral_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:20:20.768771+00:00
-- url     : https://prove2.me/theorems/d9cad35c-6a43-4bd6-b0eb-28ac791b29af
-- title:
--   Evaluation of $\int_a^\infty x^{-\sigma-1}\log x\,dx$ in closed form
-- statement:
--   Let $a, \sigma \in \mathbb{R}$ with $a \geq 1$ and $\sigma > 0$. Then the improper integral of $x^{-\sigma-1}\log x$ over $(a,\infty)$ has the closed-form value
--   $$\int_a^\infty x^{-\sigma-1} \log x \, dx = \frac{1}{\sigma^2}\, a^{-\sigma} + \frac{1}{\sigma}\, a^{-\sigma} \log a.$$
--
--   The formula follows from the explicit antiderivative $-\bigl(\sigma^{-2} t^{-\sigma} + \sigma^{-1} t^{-\sigma}\log t\bigr)$, which tends to $0$ as $t \to \infty$ and evaluates to the right-hand side at $t = a$.
--
--   This exact evaluation converts the Euler-Maclaurin remainder estimate for $\zeta'(s)$ into a fully explicit bound: in the PNT+ zeta-bounds development the tail error is controlled precisely by this integral. As a standalone identity it is reusable whenever moments of $\log$ against power decay must be computed explicitly.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1656-L1662

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
open MeasureTheory

theorem DerivUpperBnd_aux7_integral_eq {a σ : ℝ} (ha : 1 ≤ a) (σpos : 0 < σ) :
    ∫ (x : ℝ) in Ioi a, x ^ (-σ - 1) * Real.log x =
      1 / σ^2 * a ^ (-σ) + 1 / σ * a ^ (-σ) * Real.log a := by sorry
