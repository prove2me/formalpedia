-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_copy_gadget_correct
-- name    : CorrelatedAuctionComplexity.Main.copy_gadget_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:26.527795+00:00
-- url     : https://prove2.me/theorems/878c9605-920d-4a19-acfb-a187f2a44e41
-- title:
--   Lemma 12 — COPY with zero output influence
-- statement:
--   Consider any ambient binary-bid HDFPA containing the COPY roles and its seven specified edges with multiplier $\Lambda>0$. Its auxiliaries occur only in this occurrence, and the total weight outside it incident to $x$ is at most $\Lambda/2$. Then every $\eta$-NE satisfies
--
--   $$|p(x)-p(y)|\le300\eta.$$
--
--   Furthermore every legal mixed profile, regardless of equilibrium, satisfies $\Delta_y^R(p)=0$. Both clauses apply with arbitrary permitted outside edges.
--
--   Differences from the source:
--   - encoding: bidders indexed by [n], with real legal mixed profiles → finite bidder types and explicit real lottery weights, with support and no-overbidding predicates; reason: finite reindexing and finite-sum expectations preserve every supported type and deviation
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Lemma 12, p. 16 (PDF p. 16)

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main

theorem copy_gadget_correct {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 4) (hB : H.bids = {0,1})
    (y x h : N) (z : Fin 3 → N) (hroles : CopyRoles H y x h z)
    (Λ : ℝ) (hΛ : 0 < Λ)
    (ids : Fin (copyGadget y x h z).auctions.length → Fin H.edges.length)
    (hocc : Occurs H (copyGadget y x h z) ids Λ)
    (hout : (∑ e ∈ Finset.univ \ gadgetEdges H (copyGadget y x h z) ids,
      if x ∈ (H.edge e).participants then ((H.edge e).weight : ℝ) else 0) ≤ Λ/2)
    (p : N → ℝ) (hp : H.LegalBinary p) (η : ℝ) (hη : 0 ≤ η) :
    (H.IsNE η (H.binaryProfile p) → |p x - p y| ≤ 300*η) ∧
      H.delta p (gadgetEdges H (copyGadget y x h z) ids) y = 0 := by sorry

end CorrelatedAuctionComplexity.Main
