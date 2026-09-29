-- Prove2me | Theorems.Thm_Finset_Icc0_eq
-- name    : Finset.Icc0_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:01:33.138635+00:00
-- url     : https://prove2.me/theorems/9b378a89-7962-48f8-83f6-111fb43a7fe9
-- title:
--   Splitting the finite interval $\{0,\dots,N\}$ as $\{0\} \cup \{1,\dots,N\}$
-- statement:
--   For every natural number $N$, the finite integer interval $[0, N] = \{0, 1, \dots, N\}$ decomposes as
--   $$\{0, 1, \dots, N\} = \{0\} \cup \{1, \dots, N\},$$
--   i.e. in Lean's `Finset` language, $\mathrm{Icc}\,0\,N = \{0\} \cup \mathrm{Icc}\,1\,N$. (When $N = 0$ the right-hand interval $\{1,\dots,0\}$ is empty and both sides are $\{0\}$.)
--
--   This elementary set identity is used to peel off the $n = 0$ term from finite sums indexed by $\{0,\dots,N\}$ — in the PNT+ project, from the partial sums $\sum_{n \le N} n^{-s}$ that appear in the truncated Euler-Maclaurin representation $\zeta_0$ of the Riemann zeta function, where the $n = 0$ term vanishes and the meaningful range is $1 \le n \le N$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1431-L1438

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

theorem Finset.Icc0_eq (N : ℕ) : Finset.Icc 0 N = {0} ∪ Finset.Icc 1 N := by sorry
