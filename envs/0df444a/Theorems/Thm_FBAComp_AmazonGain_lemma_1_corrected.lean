-- Prove2me | Theorems.Thm_FBAComp_AmazonGain_lemma_1_corrected
-- name    : FBAComp.AmazonGain.lemma_1_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:12.786554+00:00
-- url     : https://prove2.me/theorems/f2160fb4-46df-4b34-a5b1-cf992c7c8545
-- title:
--   Lemma 1, p. 14 (corrected: c ≤ T∗) — the seller charges more with FBA
-- statement:
--   Fix the standing parameters and a cross-service sensitivity $\eta\in(0,\alpha)$. Let $(w^*_N,p^*_{A,N},p^*_{S,N})$ be a no-FBA subgame-perfect equilibrium, and let $(T^*,w^*_F,p^*_{A,F},p^*_{S,F})$ solve Amazon's fee problem (5) with benchmark $\Pi^*_{S,N}$. If the equilibrium FBA fee is at least the fulfillment cost, $T^*\ge c$, then the third-party seller's equilibrium price is strictly higher with FBA:
--
--   $$p^*_{S,F}>p^*_{S,N}.$$
--
--   This is the price comparison behind the paper's discussion of how FBA raises the seller's product value and selling cost.
--
--   **Formalization Note.** The paper states the lemma without a condition on the fee; its proof (p. 35) concludes positivity "with $\alpha>\eta$ and $T^*>c$". The optimal fee $T^*=\min\{\widetilde T,\bar T\}$ can fall below $c$, and then the printed lemma can fail, so the proof's hypothesis is added in the weak form $c\le T^*$, which suffices. The interior hypothesis is not needed and not imposed.
-- source:
--   Lai, Liu, Xiao & Zhao, “Fulfilled by Amazon”, SSRN preprint 3270958 (PDF of 2021-10-08), p. 14, Lemma 1; proof p. 35 (corrected with the proof's hypothesis on T∗)

import Mathlib
import Definitions.Def_FBAComp_AmazonGain_Model

namespace FBAComp.AmazonGain

/-- Lemma 1, p. 14 (proof p. 35), corrected with the proof's hypothesis on the fee:
when the equilibrium FBA fee is at least the fulfillment cost `c`, the seller's
equilibrium price is strictly higher with FBA than without. -/
theorem lemma_1_corrected (P : Params) (hP : P.Standing)
    (η wN pAN pSN T wF pAF pSF : ℝ) (hη : η ∈ Set.Ioo 0 P.α)
    (hN : IsEqN P η wN pAN pSN)
    (hF : IsFeeOptimal P η (profitSN P η pAN pSN) T wF pAF pSF)
    (hTc : P.c ≤ T) :
    pSN < pSF := by sorry

end FBAComp.AmazonGain
