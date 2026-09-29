-- Prove2me | Theorems.Thm_DerivUpperBnd_aux4
-- name    : DerivUpperBnd_aux4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:07:42.684214+00:00
-- url     : https://prove2.me/theorems/0d705a5e-73db-4ec9-94c2-c0568350ee8c
-- title:
--   Euler–Maclaurin half-term $\log N \cdot N^{-s}/2$ is $O(e^A \log|t|)$
-- statement:
--   Let $A, \sigma, t$ be real with $|t| > 3$ and $\sigma \in \big[1 - A/\log|t|,\, 2\big]$. Set $N = \lfloor |t| \rfloor$ and $s = \sigma + it$, and assume $N > 0$, $N \le |t|$, $s \neq 1$, and $\sigma > 1/2$. Then
--   $$\Big\| \frac{(\log N)\, N^{-s}}{2} \Big\| \;\le\; e^{A}\, \log |t|.$$
--
--   Indeed $|N^{-s}| = N^{-\sigma} \le N^{-1} \cdot N^{1-\sigma} \le e^{A}$ (using $N \ge 1$ and $\sigma \ge 1 - A/\log|t|$ with $N \le |t|$), and $\log N \le \log |t|$; the factor $1/2$ is absorbed.
--
--   This bounds the derivative of the midpoint correction term $\tfrac{1}{2} N^{-s}$ in the truncated Euler–Maclaurin representation of $\zeta(s)$; it is one of the bookkeeping estimates feeding the bound $|\zeta'(\sigma+it)| \ll \log^2 |t|$ used for $\zeta'/\zeta$ control in the Prime Number Theorem with error term.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1521-L1533

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

theorem DerivUpperBnd_aux4 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖↑(N : ℝ).log * (N : ℂ) ^ (-s) / 2‖ ≤ A.exp * |t|.log := by sorry
