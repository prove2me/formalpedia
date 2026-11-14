-- Prove2me | Theorems.Thm_ConsistentSubmodular_Shadow_LeftLaw_integral_adaptation
-- name    : ConsistentSubmodular.Shadow.LeftLaw.integral_adaptation
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:33.641203+00:00
-- url     : https://prove2.me/theorems/6c28e0d7-d83a-44f6-ac3b-9077dca7b8d8
-- title:
--   Identity (11) — $\int_0^Y\bigl(1-g(y+1)/g(y)\bigr)\,dy=C-1$
-- statement:
--   Let $\ell_J$ be a random left endpoint with finite support: weights $p_j$ on points $\ell_j$, distribution function $W$, ramp $H(x)=\sum_jp_j\max(0,x-\ell_j)$, inverse $X=H^{-1}$, and $g(y)=1/W(X(y))$. Let $Y\ge0$ and assume
--   (i) $H(\ell_j)\le Y$ for every $j$ with $p_j\ne0$, and
--   (ii) $\ell_j\le X(Y)$ for every $j$.
--   Then
--   $$\int_0^Y\bigl(1-g(y+1)\,W(X(y))\bigr)\,dy\;=\;\sum_jp_j\Bigl(X\bigl(H(\ell_j)+1\bigr)-\ell_j\Bigr)-1.$$
--
--   Since $g(y)=1/W(X(y))$, the integrand is $1-g(y+1)/g(y)$, and the right side is $C-1$, where $C=\mathbb E\bigl[X(H(\ell_J)+1)-\ell_J\bigr]$ is the expected length of the extended intervals $[\ell_j,X(H(\ell_j)+1)]$. This is identity (11) of the shadow-chain argument, valid once $Y$ lies beyond every $H(\ell_j)$ and $X(Y)$ beyond every $\ell_j$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/StepIntegrals.lean#L399-L419 (`ConsistentSubmodular.Shadow.LeftLaw.integral_adaptation`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_StepIntegrals

open scoped BigOperators Topology
open MeasureTheory Filter Set
open ConsistentSubmodular ConsistentSubmodular.Shadow
open ConsistentSubmodular.Shadow.LeftLaw
variable {ι : Type*} [Fintype ι] (L : LeftLaw ι)

theorem ConsistentSubmodular.Shadow.LeftLaw.integral_adaptation {Y : ℝ} (hY : 0 ≤ Y)
    (hS : ∀ j, L.prob j ≠ 0 → L.ramp (L.left j) ≤ Y) (hX : ∀ j, L.left j ≤ L.inv Y) :
    ∫ y in (0 : ℝ)..Y, (1 - L.slope (y + 1) * L.cdf (L.inv y)) =
      ∑ j, L.prob j * (L.inv (L.ramp (L.left j) + 1) - L.left j) - 1 := by sorry
