-- Prove2me | Theorems.Thm_ConsistentSubmodular_Chains_qStar_bounds
-- name    : ConsistentSubmodular.Chains.qStar_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:24.82207+00:00
-- url     : https://prove2.me/theorems/6902dae1-e8df-4a37-a8ba-d46136d8cc51
-- title:
--   Bounds (13) — numerical bounds on $q=(1-\xi^\star)/\xi^\star$
-- statement:
--   Let $q=(1-\xi^\star)/\xi^\star$. Then
--   $$\frac{259}{1000}\ <\ q\ <\ \frac{13}{50}.$$
--
--   These are the bounds (13), obtained from the signs $Q(259/1000)>0>Q(13/50)$ of the quartic $Q(t)=t^4+t^3-22t^2-87t+24=(1+t)^4\Psi\big(1/(1+t)\big)$. They provide the numerical control of the constant $q$ used in the analysis of the hard coverage instance.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Constants.lean#L198-L212 (`ConsistentSubmodular.Chains.qStar_bounds`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Constants

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem ConsistentSubmodular.Chains.qStar_bounds : (259 : ℝ) / 1000 < qStar ∧ qStar < 13 / 50 := by sorry
