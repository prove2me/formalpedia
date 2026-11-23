-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_dfpa_fixed_accuracy_membership
-- name    : CorrelatedAuctionComplexity.Main.dfpa_fixed_accuracy_membership
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T05:30:29.731453+00:00
-- url     : https://prove2.me/theorems/7758f57e-5d21-47d3-93a9-8bfff4cdc5c8
-- title:
--   Fixed-accuracy DFPA membership in PPAD
-- statement:
--   For every fixed positive rational accuracy $\varepsilon$, the normalized discrete first-price auction search problem is in PPAD:
--
--   $$
--   0<\varepsilon\quad\Longrightarrow\quad \mathrm{DFPA}_{\varepsilon}\in\mathrm{PPAD}.
--   $$
--
--   The input explicitly lists a finite rational bid set and correlated prior, and an answer is an explicitly coded legal rational $\varepsilon$-approximate mixed Bayes–Nash equilibrium satisfying the polynomial witness bound. This is the fixed-accuracy consequence of Lemma 20, in which the positive accuracy is instead supplied in binary as part of the input: prepend the code of the now-fixed $\varepsilon$ to each auction instance and leave equilibrium answers unchanged.
--
--   **Formalization Note** `dAuctionSearch ε` uses the same canonical instance and answer records, conditional equilibrium inequalities, no-overbidding condition, and `witnessBound` as `dVariableAccuracy`; `InPPAD` includes both TFNP membership and a polynomial-time search reduction to End-of-Line.
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Lemma 20 and proof, Section 5.2, p. 24 (PDF p. 24); fixed-accuracy specialization used for Theorem 1, p. 3.

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

theorem CorrelatedAuctionComplexity.Main.dfpa_fixed_accuracy_membership (ε : ℚ) (hε : 0 < ε) :
    InPPAD (dAuctionSearch ε) := by sorry
