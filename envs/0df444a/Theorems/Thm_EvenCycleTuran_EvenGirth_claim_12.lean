-- Prove2me | Theorems.Thm_EvenCycleTuran_EvenGirth_claim_12
-- name    : EvenCycleTuran.EvenGirth.claim_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:28:48.767729+00:00
-- url     : https://prove2.me/theorems/2bd77efc-9f03-47ab-8afd-31d5abdb76bb
-- title:
--   Claim 12, p. 20 — in a graph of girth ≥ 2l, two distinct 2l-cycles sharing a path of length l−1 meet in exactly a path of length l−1 or l
-- statement:
--   Let $l\ge2$ and let $G$ be a graph with no cycle of length $3,\dots,2l-1$ (girth at least $2l$). If $C$ and $C'$ are two distinct $2l$-cycles of $G$ that share a path of length $l-1$, then their intersection $C\cap C'$ (common vertices and common edges) is exactly a path of length $l-1$ or of length $l$.
--
--   The claim controls how two $2l$-cycles through a common path can overlap; it is used in Claim 14 to glue cycles into longer ones.
--
--   **Formalization Note.** The cycles are subgraphs of $G$ isomorphic to `cycleGraph (2 * l)`, the shared path is a subgraph of both isomorphic to `pathGraph l`, and the intersection is the subgraph infimum `C ⊓ C'`, which is required to be isomorphic to `pathGraph l` or `pathGraph (l + 1)`. The hypothesis $C\ne C'$ is implicit on the page (two equal cycles intersect in a cycle).
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 20, Claim 12 (standing hypothesis "G has girth at least 2l", p. 20)

import Mathlib
import Definitions.Def_EvenCycleTuran_EvenGirth_Setting
open SimpleGraph Finset Filter Asymptotics

namespace EvenCycleTuran.EvenGirth

theorem claim_12 {V : Type*} (G : SimpleGraph V) (l : ℕ) (hl : 2 ≤ l)
    (hG : EvenCycleTuran.C4Count.CycleFree (Set.Icc 3 (2 * l - 1)) G)
    (C C' : G.Subgraph) (hC : IsCycleCopy G (2 * l) C) (hC' : IsCycleCopy G (2 * l) C')
    (hne : C ≠ C') (Q : G.Subgraph) (hQC : IsSubpath l C Q) (hQC' : IsSubpath l C' Q) :
    ∃ r : ℕ, (r = l ∨ r = l + 1) ∧ Nonempty (pathGraph r ≃g (C ⊓ C').coe) := by sorry

end EvenCycleTuran.EvenGirth
