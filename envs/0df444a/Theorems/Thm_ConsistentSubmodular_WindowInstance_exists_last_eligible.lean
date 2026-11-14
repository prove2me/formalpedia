-- Prove2me | Theorems.Thm_ConsistentSubmodular_WindowInstance_exists_last_eligible
-- name    : ConsistentSubmodular.WindowInstance.exists_last_eligible
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:37.831503+00:00
-- url     : https://prove2.me/theorems/d8dca06d-8f12-4fa7-8705-ac8229ae004a
-- title:
--   Existence of the last eligible partner (27)
-- statement:
--   Let $W$ be a window instance with stages $0,\dots,m$, with credits $K_j=2(P_j-f(R_j))-\bigl(f(R_j\cup O_0)-f(R_j)\bigr)$ and benchmarks $P_j=f(O_j\cup R_j)$. For $\beta$ with $\beta\le\tfrac34$ let
--   $$D_\beta=\max_{0\le j\le m}\bigl(2K_j-4(1-\beta)P_j\bigr)$$
--   be the envelope. Then there is a stage $c$ with
--   $$K_c\ge D_\beta\qquad\text{and}\qquad K_j<D_\beta\ \text{ for all } j>c .$$
--
--   The stage $c=\max\{j:K_j\ge D_\beta\}$ is the last eligible partner of (27) with which $O_0$ is mixed in the half-mixture certificate of Theorem B.4.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/HalfMixtureCertificate.lean#L397-L412 (`ConsistentSubmodular.WindowInstance.exists_last_eligible`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_HalfMixtureCertificate

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.WindowInstance
variable {n : ℕ} (W : WindowInstance n)

theorem ConsistentSubmodular.WindowInstance.exists_last_eligible {β : ℝ} (hβ' : β ≤ 3 / 4) :
    ∃ c : Fin (W.lastStage + 1), W.envelope β ≤ W.credit c ∧
      ∀ j, c < j → W.credit j < W.envelope β := by sorry
