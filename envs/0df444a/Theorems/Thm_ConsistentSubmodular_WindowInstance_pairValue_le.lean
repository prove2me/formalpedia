-- Prove2me | Theorems.Thm_ConsistentSubmodular_WindowInstance_pairValue_le
-- name    : ConsistentSubmodular.WindowInstance.pairValue_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:26.604128+00:00
-- url     : https://prove2.me/theorems/e9267bcb-ae1e-45dc-931a-785bd6a5b1ca
-- title:
--   Pair value at a stage is at most the mixture value of the edge point
-- statement:
--   Let $W$ be a window instance with objective $f$, arrivals $R_j$ and candidates $O_i$, $i=0,\dots,m$. For stages $j,a,b$ and $s\in[0,1]$ let
--   $$H^{\mathrm{pair}}_j(a,b;s)=s(1-s)f(R_j)+(1-s)^2f(R_j\cup O_a)+s^2f(R_j\cup O_b)+s(1-s)f(R_j\cup O_a\cup O_b)$$
--   be the two-type value with independent selection probabilities $1-s$ and $s$. Let $H_j$ be the mixture value (3) and $(1-s)\delta_a+s\delta_b$ the point of the edge between the vertices $\delta_a$ and $\delta_b$. Then
--
--   $$H^{\mathrm{pair}}_j(a,b;s)\;\le\;H_j\big((1-s)\delta_a+s\delta_b\big).$$
--
--   For $a\ne b$ this is an equality (the two-type value of Lemma B.3); for $a=b$ merging the two labels of one core can only increase every value, giving the inequality.
--
--   The result lets the two-type estimates of Lemma B.3 be applied to edges of a polygonal path, including degenerate edges.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/WindowBounds.lean#L253-L283 (`ConsistentSubmodular.WindowInstance.pairValue_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_WindowBounds

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]
open ConsistentSubmodular.WindowInstance
variable {n : ℕ} (W : WindowInstance n)

theorem ConsistentSubmodular.WindowInstance.pairValue_le (j a b : Fin (W.lastStage + 1)) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    W.pairValue j a b s ≤ W.mixtureValue j (mix (vertex a) (vertex b) s) := by sorry
