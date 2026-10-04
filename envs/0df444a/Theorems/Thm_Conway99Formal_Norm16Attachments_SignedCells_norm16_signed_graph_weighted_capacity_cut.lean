-- Prove2me | Theorems.Thm_Conway99Formal_Norm16Attachments_SignedCells_norm16_signed_graph_weighted_capacity_cut
-- name    : Conway99Formal.Norm16Attachments.SignedCells.norm16_signed_graph_weighted_capacity_cut
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T02:50:12.35898+00:00
-- url     : https://prove2.me/theorems/a7e30e32-7723-4516-b7f6-30caa0589907
-- title:
--   Signed graph attachment capacity cut
-- statement:
--   Let G be an actual strongly regular graph with parameters (99,14,1,2), and let its vertices be labeled into P, M, Z, R, T cells satisfying the four stated independence and anticompleteness conditions. Suppose each R vertex has selected positive and negative neighbors with the stated adjacency indicator laws, and each selected pair lies in its packet-specific finite allowed set. Then, for every rational weighting of the five exact P–M, P–Z, M–Z, P–T, and M–T graph demand families, the weighted sum of demands is at most the sum over R of the maximum weighted contribution among that vertex’s allowed pairs. The conclusion is conditional on these graph, signed-cell, neighbor, and local-membership hypotheses; it does not force a universal score or exclude every norm-16 packet.
-- source:
--   Conway99 signed-attachment family, formalization/2026-10-03/norm16-attachments/BlockEquations.lean, five graph demand equations and graph_weighted_capacity_cut; source pinned at a45708acebe3f397faccb1b646be906f24f23ee5 (BlockEquations blob 2243b9ff3e16838727e0d4e03da4a5d06336d920); originating source family commit f51996b. See ATTACHMENT_AND_FORCING_BOUNDARY.md, Eq. (1), and finite weighted capacity cut Eq. (2).

import Mathlib
import Definitions.Def_norm16_signed_attachments
set_option autoImplicit false
open SimpleGraph Finset
open Conway99Formal.Norm16Attachments

theorem Conway99Formal.Norm16Attachments.SignedCells.norm16_signed_graph_weighted_capacity_cut {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (s : SignedCells G) (h : G.IsSRGWith 99 14 1 2) (c : SignedCells.SignedNeighbors G s) (allowed : SignedCells.R G s → Finset (SignedCells.P G s × SignedCells.M G s)) (hallowed : ∀ r, (c.pos r, c.neg r) ∈ allowed r) (weight : SignedCells.DemandIndex G s → ℚ) : (∑ i : SignedCells.DemandIndex G s, weight i * SignedCells.graphDemandQ G s i) ≤ ∑ r : SignedCells.R G s, (allowed r).sup' ⟨(c.pos r, c.neg r), hallowed r⟩ (fun pair => ∑ i : SignedCells.DemandIndex G s, weight i * SignedCells.graphContributionQ G s r pair i) := by sorry
