-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_expected_utility_polytime
-- name    : CorrelatedAuctionComplexity.Main.expected_utility_polytime
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:32.938272+00:00
-- url     : https://prove2.me/theorems/563ccad8-89ea-423b-9b65-5a987d52074c
-- title:
--   Lemma 15 — Polynomial-time expected utilities
-- statement:
--   For every normalized rational HDFPA $H$, legal rational mixed profile $\sigma$, and bidder $i$, there is one uniform polynomial-time bit-machine that returns the exact rational expected utility:
--
--   $$f(\operatorname{code}(H,\sigma,i))=\operatorname{code}(U_i(\sigma)).$$
--
--   The returned rational agrees exactly with the real finite-expectation definition. The auction may have arbitrarily large edges and any finite bid set. Time is polynomial in the binary input length, rather than merely in the number of rational arithmetic operations.
--
--   Differences from the source:
--   - encoding: H and σ given by their binary rational data; output the number U_i(σ) → one Cook-machine function on the request string code(H) ‖ i ‖ code(σ), returning the canonical binary code of the exact rational U_i(σ); reason: standard finite representation of the input and output; legal rational profiles are what "given σ" means computationally
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Lemma 15, p. 19 (PDF p. 19)

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

namespace CorrelatedAuctionComplexity.Main

theorem expected_utility_polytime :
    ∃ f : Bits → Bits, CookPvsNP.PolyTimeComputable f ∧
      ∀ (n : ℕ) (H : HDFPA (Fin n)), H.WellFormed 1 →
        ∀ (σ : H.RatProfile), H.Legal (H.realProfile σ) → ∀ i : Fin n,
          f (utilityRequest H σ i) = encodeRat (H.utilityQ σ i) ∧
            (H.utilityQ σ i : ℝ) = H.utility (H.realProfile σ) i := by sorry

end CorrelatedAuctionComplexity.Main
