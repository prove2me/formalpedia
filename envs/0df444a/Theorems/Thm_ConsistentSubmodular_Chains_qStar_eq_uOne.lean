-- Prove2me | Theorems.Thm_ConsistentSubmodular_Chains_qStar_eq_uOne
-- name    : ConsistentSubmodular.Chains.qStar_eq_uOne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:56.799319+00:00
-- url     : https://prove2.me/theorems/4c2c3b0c-b1c5-482a-9849-c05b615a6a02
-- title:
--   Identity $q=u_1^3(1+u_1)$ linking $q$ and the root of $\Phi$
-- statement:
--   Let $u_1$ be the root of $\Phi(x)=x^4+x^3-2x^2-3x+2$ in $(0,1)$, and $q=(1-\xi^\star)/\xi^\star$. Then
--   $$q\ =\ u_1^{3}\,(1+u_1).$$
--
--   Since $\Phi(u_1)=0$, the number $u_1^3(1+u_1)=2u_1^2+3u_1-2$ is a root of $Q(t)=t^4+t^3-22t^2-87t+24$ in $(0,1)$, hence equals $q$. This identifies the weight $u_1$ of the hard instance with the threshold $\xi^\star$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Constants.lean#L284-L299 (`ConsistentSubmodular.Chains.qStar_eq_uOne`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Constants

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem ConsistentSubmodular.Chains.qStar_eq_uOne : qStar = uOne ^ 3 * (1 + uOne) := by sorry
