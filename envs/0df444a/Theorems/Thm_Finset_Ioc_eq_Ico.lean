-- Prove2me | Theorems.Thm_Finset_Ioc_eq_Ico
-- name    : Finset.Ioc_eq_Ico
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:28:20.377738+00:00
-- url     : https://prove2.me/theorems/c30f007e-6073-4bcd-aa1b-674ea57fa145
-- title:
--   Half-open interval conversion: $(N,M] = [N+1, M+1)$ in $\mathbb{N}$
-- statement:
--   For all natural numbers $M$ and $N$, the finite open-closed interval equals a shifted half-open interval:
--   $$\{n : N < n \le M\} = \{n : N + 1 \le n < M + 1\},$$
--   i.e. $\mathrm{Ioc}\,N\,M = \mathrm{Ico}\,(N+1)\,(M+1)$ as finsets of natural numbers.
--
--   Over the integers, $N < n$ is the same as $N + 1 \le n$ and $n \le M$ is the same as $n < M+1$, so the two index sets coincide; the lemma records this as a `Finset` equality usable for rewriting sums.
--
--   Sums over ranges $N < n \le M$ arise naturally in partial summation and in splitting Dirichlet-series tails; this lemma converts them to the `Ico` normal form preferred by the summation API in the PNT+ project's zeta-function computations.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L725-L726

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

theorem Finset.Ioc_eq_Ico (M N : ℕ) : Finset.Ioc N M = Finset.Ico (N + 1) (M + 1) := by sorry
