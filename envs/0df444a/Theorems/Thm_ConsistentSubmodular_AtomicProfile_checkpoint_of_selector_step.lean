-- Prove2me | Theorems.Thm_ConsistentSubmodular_AtomicProfile_checkpoint_of_selector_step
-- name    : ConsistentSubmodular.AtomicProfile.checkpoint_of_selector_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:21.710197+00:00
-- url     : https://prove2.me/theorems/f6bb46ae-c824-4dc7-a9f3-c5d9bcc0cec9
-- title:
--   Termination of the selector relay process
-- statement:
--   Let $P$ be an atomic profile on stages $0,\dots,m$. Suppose a *step rule* is given: for every stage $h$ and every selector state $S$ at $h$ it asserts
--   $$\text{a checkpoint certificate for } P \text{ exists}\quad\text{or}\quad \exists\, s>h \text{ such that a selector state at } s \text{ exists.}$$
--   Then, if there is a selector state at some stage $h$, a checkpoint certificate for $P$ exists.
--
--   (A selector state at $h$ consists of $\tfrac34<A_h<1$, an access certificate, strong credit and a relay history; a checkpoint certificate is a point of support size at most $2$ with value at least $\tfrac34$ of the benchmark at every stage, together with safe entry and exit paths of at most $(m+1)+2$ pieces in total.)
--
--   Any complete local decision rule terminates, because every relay strictly increases the finite stage index $h\in\{0,\dots,m\}$. This turns the individual selector steps into the existence of a checkpoint certificate.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/SelectorTermination.lean#L14-L30 (`ConsistentSubmodular.AtomicProfile.checkpoint_of_selector_step`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorState

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem ConsistentSubmodular.AtomicProfile.checkpoint_of_selector_step
    (step : ∀ h, SelectorState P h → Nonempty (CheckpointCertificate P) ∨
      ∃ s, h < s ∧ Nonempty (SelectorState P s))
    (h : Fin (m + 1)) (S : SelectorState P h) : Nonempty (CheckpointCertificate P) := by sorry
