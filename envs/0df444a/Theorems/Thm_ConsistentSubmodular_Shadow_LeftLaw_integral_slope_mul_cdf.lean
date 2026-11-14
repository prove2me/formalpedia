-- Prove2me | Theorems.Thm_ConsistentSubmodular_Shadow_LeftLaw_integral_slope_mul_cdf
-- name    : ConsistentSubmodular.Shadow.LeftLaw.integral_slope_mul_cdf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:52.318403+00:00
-- url     : https://prove2.me/theorems/23532792-dde7-4e14-b3d8-9935b64217f4
-- title:
--   Fubini identity for $\int_0^Y g(y+1)\Pr[S\le y]\,dy$
-- statement:
--   Let $\ell_J$ be a random left endpoint with finite support: weights $p_j$ on points $\ell_j$, distribution function $W$, ramp $H(x)=\sum_jp_j\max(0,x-\ell_j)$, inverse $X=H^{-1}$, and $g(y)=1/W(X(y))$. Let $Y\ge0$ and suppose $H(\ell_j)\le Y$ for every $j$ with $p_j\ne0$. Then
--   $$\int_0^Y g(y+1)\,W\bigl(X(y)\bigr)\,dy\;=\;\sum_jp_j\Bigl(X(Y+1)-X\bigl(H(\ell_j)+1\bigr)\Bigr).$$
--
--   Since $W(X(y))=\Pr[S\le y]$ for the random variable $S=H(\ell_J)$ with realizations $S_j=H(\ell_j)$, this is Fubini's theorem combined with the single-realization identity $\int_0^Yg(y+1)\mathbf 1[S_j\le y]\,dy=X(Y+1)-X(S_j+1)$. It is a step in the proof of identity (11).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/StepIntegrals.lean#L335-L362 (`ConsistentSubmodular.Shadow.LeftLaw.integral_slope_mul_cdf`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_StepIntegrals

open scoped BigOperators Topology
open MeasureTheory Filter Set
open ConsistentSubmodular ConsistentSubmodular.Shadow
open ConsistentSubmodular.Shadow.LeftLaw
variable {ι : Type*} [Fintype ι] (L : LeftLaw ι)

theorem ConsistentSubmodular.Shadow.LeftLaw.integral_slope_mul_cdf {Y : ℝ} (hY : 0 ≤ Y)
    (hS : ∀ j, L.prob j ≠ 0 → L.ramp (L.left j) ≤ Y) :
    ∫ y in (0 : ℝ)..Y, L.slope (y + 1) * L.cdf (L.inv y) =
      ∑ j, L.prob j * (L.inv (Y + 1) - L.inv (L.ramp (L.left j) + 1)) := by sorry
