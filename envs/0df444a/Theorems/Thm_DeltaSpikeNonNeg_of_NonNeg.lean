-- Prove2me | Theorems.Thm_DeltaSpikeNonNeg_of_NonNeg
-- name    : DeltaSpikeNonNeg_of_NonNeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:58:19.143383+00:00
-- url     : https://prove2.me/theorems/dd63d197-9287-4282-9035-1cf8d5c0bdc4
-- title:
--   Nonnegativity of the delta spike for a nonnegative mollifier
-- statement:
--   Let $\nu : \mathbb{R} \to \mathbb{R}$ satisfy $\nu(x) \ge 0$ for all $x > 0$, and let $x > 0$ and $\varepsilon > 0$ be real. Then the delta spike
--   $$\mathrm{DeltaSpike}_{\nu,\varepsilon}(x) \;=\; \frac{1}{\varepsilon}\, \nu\!\big(x^{1/\varepsilon}\big) \;\ge\; 0.$$
--
--   For $x > 0$ the rescaled argument $x^{1/\varepsilon}$ is again positive, so the hypothesis applies to it, and dividing by the positive scale $\varepsilon$ preserves the sign.
--
--   Nonnegativity of the spike is what makes the smoothed Chebyshev function $\psi_\varepsilon$ a genuine weighted count of prime powers with nonnegative weights; this is used when comparing $\psi_\varepsilon$ with the unsmoothed $\psi$ via monotonicity in the extraction of the Prime Number Theorem from the smoothed asymptotic.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L735-L741

import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Definitions.Def_MellinCalculus_defs

open scoped ContDiff

set_option lang.lemmaCmd true

-- TODO: move near `MeasureTheory.setIntegral_prod`

-- How to deal with this coercion?... Ans: (f ·)
--- noncomputable def funCoe (f : ℝ → ℝ) : ℝ → ℂ := fun x ↦ f x

open Complex Topology Filter Real MeasureTheory Set

variable {𝕂 : Type*} [RCLike 𝕂]

-- TODO: generalize to `RCLike`

local notation (name := mellintransform) "𝓜" => mellin

-- filter-free version:

-- This lemma might not be necessary, but the RHS is supported on [0, infinity), which makes
-- results like `support_MellinConvolution_subsets` easier to apply.

/-% ** Wrong delimiters on purpose, no need to include this in the LaTeX outline
\begin{lemma}[Smooth1Properties_estimate]\label{Smooth1Properties_estimate}
\lean{Smooth1Properties_estimate}\leanok
For $\epsilon>0$,
$$
  \log2>\frac{1-2^{-\epsilon}}\epsilon
$$
\end{lemma}
%-/

theorem DeltaSpikeNonNeg_of_NonNeg {ν : ℝ → ℝ} (νnonneg : ∀ x > 0, 0 ≤ ν x)
     {x ε : ℝ} (xpos : 0 < x) (εpos : 0 < ε) :
    0 ≤ DeltaSpike ν ε x := by sorry
