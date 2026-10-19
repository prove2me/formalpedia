-- Prove2me | Theorems.Thm_FBAComp_AmazonGain_lemma_3
-- name    : FBAComp.AmazonGain.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:24.551682+00:00
-- url     : https://prove2.me/theorems/f23d19e7-8ffd-4ac7-a2ba-609a4a9bd40b
-- title:
--   Lemma 3, p. 15 — the seller sells more with FBA: q∗S,F ≥ q∗S,N
-- statement:
--   Fix the standing parameters and a cross-service sensitivity $\eta\in(0,\alpha)$. Let $(w^*_N,p^*_{A,N},p^*_{S,N})$ be a no-FBA subgame-perfect equilibrium, and let $(T^*,w^*_F,p^*_{A,F},p^*_{S,F})$ solve Amazon's fee problem (5) with the seller's no-FBA profit $\Pi^*_{S,N}$ as participation benchmark. Then the third-party seller's equilibrium sales are at least as large with FBA as without:
--
--   $$q^*_{S,F}=Q_S-p^*_{S,F}+\beta p^*_{A,F}+\alpha s_A-\eta s_A\ \ge\ q^*_{S,N}=Q_S-p^*_{S,N}+\beta p^*_{A,N}+\alpha s_S-\eta s_A.$$
--
--   The paper remarks that this conclusion, unlike Lemma 1, depends on the participation constraint on the fee.
--
--   **Formalization Note.** Fee feasibility in (5) includes the added clause $q^*_{S,F}\ge 0$ (see the model definition). The interior hypothesis is not needed for this statement and is not imposed.
-- source:
--   Lai, Liu, Xiao & Zhao, “Fulfilled by Amazon”, SSRN preprint 3270958 (PDF of 2021-10-08), p. 15, Lemma 3; proof p. 35

import Mathlib
import Definitions.Def_FBAComp_AmazonGain_Model

namespace FBAComp.AmazonGain

/-- Lemma 3, p. 15 (proof p. 35): the seller's equilibrium sales are at least as high
with FBA as without. -/
theorem lemma_3 (P : Params) (hP : P.Standing)
    (η wN pAN pSN T wF pAF pSF : ℝ) (hη : η ∈ Set.Ioo 0 P.α)
    (hN : IsEqN P η wN pAN pSN)
    (hF : IsFeeOptimal P η (profitSN P η pAN pSN) T wF pAF pSF) :
    qSN P η pAN pSN ≤ qSF P η pAF pSF := by sorry

end FBAComp.AmazonGain
