-- Prove2me | Theorems.Thm_ConsistentSubmodular_exists_two_labels_of_supportCard
-- name    : ConsistentSubmodular.exists_two_labels_of_supportCard
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:00.478893+00:00
-- url     : https://prove2.me/theorems/c73935f2-a28d-4a13-b603-c22ff5420118
-- title:
--   A point with support size at most two lives on two labels
-- statement:
--   Let $p\in\mathbb R^{\{0,\dots,m\}}$ be a point whose number of nonzero coordinates is at most $2$. Then there are labels $a,b\in\{0,\dots,m\}$ such that $p_i=0$ for every $i\notin\{a,b\}$.
--
--   This converts the cardinality form of the two-label support condition on checkpoint points into an explicit pair of labels, which is used when a checkpoint is verified as a two-vertex mixture.
--
--   **Formalization Note**: $a$ and $b$ are not required to be distinct, so the case of a point supported on a single label (or of zero support) is included.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/WindowCertificates.lean#L18-L40 (`ConsistentSubmodular.exists_two_labels_of_supportCard`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_AtomicProfiles

open scoped BigOperators
open ConsistentSubmodular

theorem ConsistentSubmodular.exists_two_labels_of_supportCard {m : ℕ} {p : Point m} (h : supportCard p ≤ 2) :
    ∃ a b : Fin (m + 1), ∀ i, i ≠ a → i ≠ b → p i = 0 := by sorry
