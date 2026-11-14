-- Prove2me | Theorems.Thm_ConsistentSubmodular_WindowInstance_bufferMixtureValue_le_average
-- name    : ConsistentSubmodular.WindowInstance.bufferMixtureValue_le_average
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:19.191206+00:00
-- url     : https://prove2.me/theorems/3f80285d-0335-490a-a76e-b18e2843695f
-- title:
--   Inequality (22) — buffer mixture value is at most the average candidate value
-- statement:
--   Let $W$ be a window instance with stages $0,\dots,m$, objective $f$ and candidates $O_0,\dots,O_m$. For a buffer $Q\subseteq[n]$ and $p\in\mathbb{R}^{m+1}$ let
--   $$H_Q(p)=\sum_{I\subseteq\{0,\dots,m\}}\Big(\prod_{i\in I}p_i\prod_{i\notin I}(1-p_i)\Big)f\Big(Q\cup\bigcup_{i\in I}O_i\Big).$$
--   If $p\in\Delta$ is a probability vector ($p_i\ge0$, $\sum_ip_i=1$), then
--
--   $$H_Q(p)\;\le\;\sum_{i=0}^{m}p_i\,f(Q\cup O_i).$$
--
--   This is inequality (22): it follows from subadditivity after contracting $Q$ together with $\Pr[i\in I(p)]=p_i$. It upper-bounds the value of a mixture by a linear average of candidate values, and is used to show that mixtures cannot beat the best convex combination of candidates (Lemma B.2).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/WindowBounds.lean#L176-L207 (`ConsistentSubmodular.WindowInstance.bufferMixtureValue_le_average`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]
open ConsistentSubmodular.WindowInstance
variable {n : ℕ} (W : WindowInstance n)

theorem ConsistentSubmodular.WindowInstance.bufferMixtureValue_le_average (Q : Finset (Fin n)) {p : Point W.lastStage}
    (hp : IsSimplex p) :
    W.bufferMixtureValue Q p ≤ ∑ i, p i * W.objective.value (Q ∪ W.candidate i) := by sorry
