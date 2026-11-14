-- Prove2me | Theorems.Thm_ConsistentSubmodular_Shadow_LeftLaw_integral_slope_after
-- name    : ConsistentSubmodular.Shadow.LeftLaw.integral_slope_after
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:45.01831+00:00
-- url     : https://prove2.me/theorems/9fedfcb8-f7ae-48d2-b857-5e3285562d89
-- title:
--   Contribution of one realization $S=H(\ell_j)$ to $\int g(y+1)\Pr[S\le y]\,dy$
-- statement:
--   Let $\ell_J$ be a random left endpoint with finite support, ramp $H$, inverse $X=H^{-1}$, and $g(y)=1/W(X(y))$, where $W$ is the distribution function of $\ell_J$. For real numbers $S,Y$ with $0\le S\le Y$,
--   $$\int_0^Y g(y+1)\,\mathbf 1[S\le y]\,dy\;=\;X(Y+1)-X(S+1).$$
--
--   The left side is the integral of $g(y+1)$ over $[S,Y]$, and $X$ is an antiderivative of $g$ almost everywhere (it is continuous with right derivative $g$). The identity gives the contribution of a single realization $S=H(\ell_j)$ to the integral $\int g(y+1)\Pr[S\le y]\,dy$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/StepIntegrals.lean#L306-L333 (`ConsistentSubmodular.Shadow.LeftLaw.integral_slope_after`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_StepIntegrals

open scoped BigOperators Topology
open MeasureTheory Filter Set
open ConsistentSubmodular ConsistentSubmodular.Shadow
open ConsistentSubmodular.Shadow.LeftLaw
variable {ι : Type*} [Fintype ι] (L : LeftLaw ι)

theorem ConsistentSubmodular.Shadow.LeftLaw.integral_slope_after {S Y : ℝ} (hS : 0 ≤ S) (hSY : S ≤ Y) :
    ∫ y in (0 : ℝ)..Y, L.slope (y + 1) * (if S ≤ y then 1 else 0) =
      L.inv (Y + 1) - L.inv (S + 1) := by sorry
