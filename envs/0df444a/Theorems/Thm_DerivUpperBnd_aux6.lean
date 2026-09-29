-- Prove2me | Theorems.Thm_DerivUpperBnd_aux6
-- name    : DerivUpperBnd_aux6
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:16:11.319074+00:00
-- url     : https://prove2.me/theorems/abca8093-e9db-44cd-bd20-a786e40087f3
-- title:
--   Arithmetic bound: $2|t| N^{-\sigma}/\sigma \le 16 e^A$ for $N = \lfloor |t| \rfloor$ near $\sigma = 1$
-- statement:
--   Let $A, \sigma, t$ be real with $|t| > 3$ and $\sigma \in \big[1 - A/\log|t|,\, 2\big]$. Set $N = \lfloor |t| \rfloor$ and assume $N > 0$, $N \le |t|$, $\sigma + it \neq 1$, and $\sigma > 1/2$. Then
--   $$\frac{2\,|t|\, N^{-\sigma}}{\sigma} \;\le\; 2\,(8\, e^{A}).$$
--
--   The key comparisons are $N^{-\sigma} \le N^{-1}\, N^{1-\sigma}$ with $N^{1-\sigma} \le |t|^{A/\log|t|} = e^{A}$, the floor bound $|t| \le 2N$ valid for $|t| > 3$ (so $|t|/N \le 2$), and $1/\sigma < 2$ from $\sigma > 1/2$; multiplying these gives the constant $16 e^A$.
--
--   This converts the natural tail-integral bound $2|t| N^{-\sigma}/\sigma$ appearing in the Euler–Maclaurin estimates for $\zeta'$ into a clean absolute constant times $e^A$, so that the tail contributions are $O(1)$ and the truncated Dirichlet sum dominates in the final $\log^2 |t|$ bound.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1561-L1573

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

theorem DerivUpperBnd_aux6 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    0 < N → ↑N ≤ |t| → ↑σ + ↑t * I ≠ 1 → 1 / 2 < σ →
    2 * |t| * ↑N ^ (-σ) / σ ≤ 2 * (8 * A.exp) := by sorry
