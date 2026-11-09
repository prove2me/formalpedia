-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_sum_gadget_correct
-- name    : CorrelatedAuctionComplexity.Main.sum_gadget_correct
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:54.548551+00:00
-- url     : https://prove2.me/theorems/3d174eff-025b-422d-bfe6-5bb1b5964dc5
-- title:
--   Lemma 13 — SUM identities and saturated-addition error
-- statement:
--   Consider any ambient binary-bid HDFPA containing the six-edge SUM gadget, with fresh auxiliaries and the specified role values. Repeated inputs $x_1=x_2$ are allowed. Assume that for every legal mixed profile, the full payoff difference of output $y$ equals its contribution from this gadget, and that $W_y\le\Gamma$. Every legal real mixed profile satisfies
--
--   $$\Delta_h^R(p)=p(y)-p(x_1)-p(x_2),\qquad\Delta_y^R(p)=1-2p(h).$$
--
--   If the profile is also an $\eta$-NE, then
--
--   $$|p(y)-\min(p(x_1)+p(x_2),1)|\le\max(300,2\Gamma)\eta.$$
--
--   The weight bound includes all edges incident to $y$.
--
--   Differences from the source:
--   - encoding: bidders indexed by [n], with real legal mixed profiles → finite bidder types and explicit real lottery weights, with support and no-overbidding predicates; reason: finite reindexing and finite-sum expectations preserve every supported type and deviation
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Lemma 13, p. 17 (PDF p. 17)

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main

theorem sum_gadget_correct {N : Type} [Fintype N] [DecidableEq N]
    (H : HDFPA N) (hH : H.WellFormed 4) (hB : H.bids = {0,1})
    (x₁ x₂ y h : N) (z : Fin 6 → N) (hroles : SumRoles H x₁ x₂ y h z)
    (ids : Fin (sumGadget x₁ x₂ y h z).auctions.length → Fin H.edges.length)
    (hocc : Occurs H (sumGadget x₁ x₂ y h z) ids 1)
    (houtput : ∀ q : N → ℝ, H.LegalBinary q →
      H.totalDelta q y = H.delta q (gadgetEdges H (sumGadget x₁ x₂ y h z) ids) y)
    (Γ : ℝ) (hΓ : H.incidentWeight y ≤ Γ)
    (p : N → ℝ) (hp : H.LegalBinary p) (η : ℝ) (hη : 0 ≤ η) :
    H.delta p (gadgetEdges H (sumGadget x₁ x₂ y h z) ids) h = p y-p x₁-p x₂ ∧
      H.delta p (gadgetEdges H (sumGadget x₁ x₂ y h z) ids) y = 1-2*p h ∧
      (H.IsNE η (H.binaryProfile p) → |p y-min (p x₁+p x₂) 1| ≤ max 300 (2*Γ)*η) := by sorry

end CorrelatedAuctionComplexity.Main
