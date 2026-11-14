-- Prove2me | Theorems.Thm_ConsistentSubmodular_AtomicProfile_selector_large_parameter
-- name    : ConsistentSubmodular.AtomicProfile.selector_large_parameter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:56.307842+00:00
-- url     : https://prove2.me/theorems/57ce558d-5031-4b6a-88ac-8a5422fa3e45
-- title:
--   Selector step for a large envelope parameter ($\rho_h \ge 4/3$)
-- statement:
--   Let $P$ be an atomic profile on stages $0,\dots,m$ (finitely many weighted atoms, each with a pool stage and a nonempty set of labels not exceeding the pool). Write $B_t$ for its baseline, $R(i,t)$ for the residual weight of label $i$ at stage $t$, $A_t=R(t,t)$ for the designated weight, and $\beta_t=B_t+A_t$ for the benchmark. A stage $t$ is *active* if $B_t<3A_t$. Let $\rho_h$ denote the raw envelope at $h$, i.e. the maximum of $0$ and of the raw ratios $\frac{4(A_t-R(h,t))-(\beta_t-A_h)-3(1-A_h)}{A_h-R(h,t)}$ over all active $t>h$. Assume $P$ is canonical ($A_0=1$ and $R(i,t)\le A_t$ for all $i,t$). A *selector state* at $h$ consists of $\tfrac34<A_h<1$, an access certificate (a safe polygonal path of at most $h$ pieces from vertex $0$ to vertex $h$ keeping value at least $\tfrac34$ at stage $0$), strong credit at $h$, and a relay history ending at $h$ (a high, accessible parent stage $<h$ together with a parameter in $[1,3)$ and the relay-edge inequalities). A *checkpoint certificate* for $P$ is a point of the simplex with support size at most $2$, with value at least $\tfrac34\beta_t$ at every stage $t$, together with safe entry and exit polygonal paths from vertex $0$ and to the last vertex, using in total at most $(m+1)+2$ affine pieces.
--
--   **Statement.** If $\rho_h\ge \tfrac43$ and $S$ is a selector state at $h$, then
--   $$\text{a checkpoint certificate for } P \text{ exists}\quad\text{or}\quad \exists\, s>h \text{ such that a selector state at } s \text{ exists.}$$
--   This is one step of the selector argument: a selector state is either converted into a checkpoint certificate or relayed to a strictly later selector state, so the process must end in a checkpoint certificate.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/SelectorRelays.lean#L60-L93 (`ConsistentSubmodular.AtomicProfile.selector_large_parameter`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorState

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem ConsistentSubmodular.AtomicProfile.selector_large_parameter (hP : P.Canonical) (h : Fin (m + 1))
    (S : SelectorState P h) (hq : (4 : ℝ) / 3 ≤ P.rawEnvelope h) :
    Nonempty (CheckpointCertificate P) ∨ ∃ s, h < s ∧ Nonempty (SelectorState P s) := by sorry
