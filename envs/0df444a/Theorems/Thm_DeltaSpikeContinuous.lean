-- Prove2me | Theorems.Thm_DeltaSpikeContinuous
-- name    : DeltaSpikeContinuous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:58:05.364632+00:00
-- url     : https://prove2.me/theorems/9ced8dcb-c111-4823-b00c-b9e004bb276e
-- title:
--   Continuity of the Mellin delta spike $x \mapsto \nu(x^{1/\varepsilon})/\varepsilon$
-- statement:
--   Let $\nu : \mathbb{R} \to \mathbb{R}$ be a mollifier of class $C^1$ and let $\varepsilon > 0$. The delta spike at scale $\varepsilon$ is the rescaled function
--   $$\mathrm{DeltaSpike}_{\nu,\varepsilon}(x) \;=\; \frac{1}{\varepsilon}\, \nu\!\big(x^{1/\varepsilon}\big),$$
--   the multiplicative-convolution analogue of an approximate identity concentrating at $x = 1$ as $\varepsilon \to 0$. The theorem asserts that under these hypotheses the function $x \mapsto \mathrm{DeltaSpike}_{\nu,\varepsilon}(x)$ is continuous on $\mathbb{R}$.
--
--   Continuity follows from the continuity of $\nu$ (guaranteed by $C^1$ smoothness) composed with the continuous real-power map $x \mapsto x^{1/\varepsilon}$.
--
--   In the Mellin-calculus framework of PNT+, the delta spike is the kernel whose multiplicative convolution with the indicator of $[0,1]$ produces the smoothed cutoff $\mathrm{Smooth1}$ used to define the smoothed Chebyshev function; its continuity is a basic prerequisite for integrability and for computing its Mellin transform.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L489-L493

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

@[fun_prop]

theorem DeltaSpikeContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ DeltaSpike ν ε x) := by sorry
