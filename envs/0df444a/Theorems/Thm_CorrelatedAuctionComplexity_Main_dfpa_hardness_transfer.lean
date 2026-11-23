-- Prove2me | Theorems.Thm_CorrelatedAuctionComplexity_Main_dfpa_hardness_transfer
-- name    : CorrelatedAuctionComplexity.Main.dfpa_hardness_transfer
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T05:34:16.745852+00:00
-- url     : https://prove2.me/theorems/d8320729-c971-407b-bbe3-772269231ea1
-- title:
--   Section 5.1 — Hardness transfer from HDFPA to three-bid DFPA
-- statement:
--   Let $\eta>0$, and suppose that finding Nash equilibria is PPAD-hard for normalized HDFPAs at accuracy $\eta/4$, with bid set $\{0,1/4\}$ and at most four participants per edge. Then equilibrium computation for normalized DFPAs is PPAD-hard at accuracy $\eta/605$, both in general and when the bid set is restricted to $\{0,1/5,2/5\}$:
--
--   $$
--   \mathrm{HDFPA}_{\eta/4,\ B=\{0,1/4\},\ |S_e|\le4}\ \text{is PPAD-hard}
--   \quad\Longrightarrow\quad
--   \mathrm{DFPA}_{\eta/605}\ \text{and}\ \mathrm{DFPA}_{\eta/605,\ B=\{0,1/5,2/5\}}\ \text{are PPAD-hard}.
--   $$
--
--   The reduction is the construction of Section 5.1. Rescaling by $4$ produces an HDFPA with values in $\{1/2,2,3,4\}$ and bids $\{0,1\}$. The shifted DFPA adds fifty value-zero dummy bidders and anchor masses. From an $(\eta/121)$-approximate MBNE, one extracts $\sigma_i(1)=\beta_{x_i}(v_i+1)(2)$. Lemma 17 bounds each suppressed zero-bid probability by $10\varepsilon'$, and the utility comparison loses at most $121\varepsilon'W_i$, so $\sigma$ is an $\eta$-NE. Dividing all bids and values by $5$ yields the final normalized accuracy $\eta/605$ and the stated three bids.
--
--   **Formalization Note** The search problems use explicit canonical rational records and polynomially bounded rational answers. The general hardness clause follows by including the restricted valid instances in the unrestricted problem. The parent reduction imports `suppress_zero_bids`, which is precisely Lemma 17 used by this transfer.
-- source:
--   Mark Chen, Xi Chen, Hao Cui, William Pires, Jonah Stockwell, STOC 2027 submission #324 (October 2026), Section 5.1, pp. 21–24 (PDF pp. 21–24), especially the hardness proof on pp. 22–23 and final normalization on p. 23; uses Lemma 17, pp. 22–24.

import Definitions.Def_CorrelatedAuctionComplexity_Main_MembershipTools

set_option autoImplicit false

theorem CorrelatedAuctionComplexity.Main.dfpa_hardness_transfer (η : ℚ) (hη : 0 < η)
    (hhard : PPADHard (hAuctionSearch (normalizedHAccuracy η) true)) :
    PPADHard (dAuctionSearch (normalizedDAccuracy η)) ∧
      PPADHard (dAuctionSearch (normalizedDAccuracy η) true) := by sorry
