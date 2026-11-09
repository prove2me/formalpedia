-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_not_gadget_correct
-- name    : CorrelatedAuctionComplexity.Main.not_gadget_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:20.08861+00:00
-- url     : https://prove2.me/theorems/1ab49d1c-322a-42c0-bce1-b3187499b140
-- title:
--   Lemma 14 — NOT identities and complement error
-- statement:
--   Consider any ambient binary-bid HDFPA containing the five-edge NOT gadget, with fresh auxiliaries and the specified role values. Assume that for every legal profile the full output payoff difference equals its gadget contribution, and $W_y\le\Gamma$. Every legal real mixed profile satisfies
--
--   $$\Delta_h^R(p)=p(y)-(1-p(x)),\qquad\Delta_y^R(p)=1-2p(h).$$
--
--   If the profile is an $\eta$-NE, then
--
--   $$|p(y)-(1-p(x))|\le\max(300,2\Gamma)\eta.$$
--
--   The identities do not require an equilibrium assumption, and arbitrary allowed outside edges remain present.
--
--   Differences from the source:
--   - encoding: bidders indexed by [n], with real legal mixed profiles → finite bidder types and explicit real lottery weights, with support and no-overbidding predicates; reason: finite reindexing and finite-sum expectations preserve every supported type and deviation
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Lemma 14, p. 18 (PDF p. 18)

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main

theorem not_gadget_correct {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 4) (hB : H.bids = {0,1})
    (x y h : N) (z : Fin 2 → N) (hroles : NotRoles H x y h z)
    (ids : Fin (notGadget x y h z).auctions.length → Fin H.edges.length)
    (hocc : Occurs H (notGadget x y h z) ids 1)
    (houtput : ∀ q : N → ℝ, H.LegalBinary q →
      H.totalDelta q y = H.delta q (gadgetEdges H (notGadget x y h z) ids) y)
    (Γ : ℝ) (hΓ : H.incidentWeight y ≤ Γ)
    (p : N → ℝ) (hp : H.LegalBinary p) (η : ℝ) (hη : 0 ≤ η) :
    H.delta p (gadgetEdges H (notGadget x y h z) ids) h = p y-(1-p x) ∧
      H.delta p (gadgetEdges H (notGadget x y h z) ids) y = 1-2*p h ∧
      (H.IsNE η (H.binaryProfile p) → |p y-(1-p x)| ≤ max 300 (2*Γ)*η) := by sorry

end CorrelatedAuctionComplexity.Main
