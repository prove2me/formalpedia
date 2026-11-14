-- Prove2me | Theorems.Thm_ConsistentSubmodular_WindowInstance_prefix_bound
-- name    : ConsistentSubmodular.WindowInstance.prefix_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:09.334076+00:00
-- url     : https://prove2.me/theorems/81b393a0-574d-4506-a1bf-d7c7f8c1ac47
-- title:
--   Lemma B.5 — the prefix bound
-- statement:
--   Let $W$ be a window instance with stages $0,\dots,m$, arrival prefixes $R_j$, candidates $O_j$, and objective $f$. For a stage $j$ write $\lambda_j=f(R_j)$ (arrival value), $r_{i,j}=f(R_j\cup O_i)-\lambda_j$ (residual), $K_j=2g_j-r_{0,j}$ (credit, where $g_j=P_j-\lambda_j$ and $P_j=f(O_j\cup R_j)$), and
--   $$H_j(O_0,O_c;\tfrac12)=\tfrac14\Bigl[f(R_j)+f(R_j\cup O_0)+f(R_j\cup O_c)+f(R_j\cup O_0\cup O_c)\Bigr]$$
--   for the two-type value at the midpoint. Then for all stages $j\le c$,
--   $$4\lambda_j+2\,r_{0,j}+K_c\;\le\;4\,H_j\bigl(O_0,O_c;\tfrac12\bigr).$$
--
--   This is inequality (29) of the paper multiplied by four. It bounds the value of the half mixture of $O_0$ and the partner $O_c$ at every stage up to $c$ from below, and is used for the persistence of the half-mixture anchor on the prefix of the window.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/HalfMixtureCertificate.lean#L118-L138 (`ConsistentSubmodular.WindowInstance.prefix_bound`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_WindowBounds

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.WindowInstance
variable {n : ℕ} (W : WindowInstance n)

theorem ConsistentSubmodular.WindowInstance.prefix_bound {j c : Fin (W.lastStage + 1)} (hjc : j ≤ c) :
    4 * W.arrivalValue j + 2 * W.residual 0 j + W.credit c ≤ 4 * W.pairValue j 0 c (1 / 2) := by sorry
