-- Prove2me | Theorems.Thm_ConsistentSubmodular_Shadow_LeftLaw_inv_right
-- name    : ConsistentSubmodular.Shadow.LeftLaw.inv_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:57.517338+00:00
-- url     : https://prove2.me/theorems/2b5989e9-0d4b-46b2-b687-9f3e5e621cc0
-- title:
--   The inverse $X$ is linear with slope $g(y)$ just right of $y\ge0$
-- statement:
--   Let $\ell_J$ be a random left endpoint with finite support, with distribution function $W$, ramp $H(x)=\sum_jp_j\max(0,x-\ell_j)$, inverse $X=H^{-1}$ (extended by $X(0)$ on negative arguments), and $g(y)=1/W(X(y))$. For every $y\ge0$ there is $\delta>0$ such that for all $t\in[y,y+\delta)$,
--   $$X(t)\;=\;X(y)+(t-y)\,g(y).$$
--
--   (Formally, the identity holds eventually as $t\to y^+$.) Thus $X$ has right derivative $g(y)$ everywhere on $[0,\infty)$.
--
--   **Formalization Note** In Lean $g(y)=1/W(X(y))$ is the real division, so a vanishing $W$ would give the junk value $0$; the statement is as given for all $y\ge0$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/StepIntegrals.lean#L245-L264 (`ConsistentSubmodular.Shadow.LeftLaw.inv_right`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_StepIntegrals

open scoped BigOperators Topology
open MeasureTheory Filter Set
open ConsistentSubmodular ConsistentSubmodular.Shadow
open ConsistentSubmodular.Shadow.LeftLaw
variable {ι : Type*} [Fintype ι] (L : LeftLaw ι)

theorem ConsistentSubmodular.Shadow.LeftLaw.inv_right {y : ℝ} (hy : 0 ≤ y) :
    ∀ᶠ t in 𝓝[≥] y, L.inv t = L.inv y + (t - y) * L.slope y := by sorry
