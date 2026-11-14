-- Prove2me | Theorems.Thm_ConsistentSubmodular_Shadow_LeftLaw_ramp_right
-- name    : ConsistentSubmodular.Shadow.LeftLaw.ramp_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:10.276721+00:00
-- url     : https://prove2.me/theorems/99f5cea0-9f9a-4a70-be39-3288412aa027
-- title:
--   The ramp $H$ is linear with slope $W(x)$ just right of $x$
-- statement:
--   Let $\ell_J$ be a random left endpoint with finite support, weights $p_j$ on points $\ell_j$. Let $W(x)=\Pr[\ell_J\le x]$ be its distribution function and $H(x)=\sum_jp_j\max(0,x-\ell_j)$. Then for every $x\in\mathbb R$ there is $\delta>0$ such that for all $h\in[0,\delta)$,
--   $$H(x+h)\;=\;H(x)+W(x)\,h.$$
--
--   (Formally, the identity holds eventually as $h\to0^+$.) The function $H$ is the integral of $W$, and $W$ is right-continuous and piecewise constant, so $H$ is linear to the right of every point with slope $W(x)$. This fact is used to compute the right derivative of the inverse $X=H^{-1}$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/StepIntegrals.lean#L226-L243 (`ConsistentSubmodular.Shadow.LeftLaw.ramp_right`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_StepIntegrals

open scoped BigOperators Topology
open MeasureTheory Filter Set
open ConsistentSubmodular ConsistentSubmodular.Shadow
open ConsistentSubmodular.Shadow.LeftLaw
variable {ι : Type*} [Fintype ι] (L : LeftLaw ι)

theorem ConsistentSubmodular.Shadow.LeftLaw.ramp_right (x : ℝ) : ∀ᶠ h in 𝓝[≥] (0 : ℝ), L.ramp (x + h) = L.ramp x + L.cdf x * h := by sorry
