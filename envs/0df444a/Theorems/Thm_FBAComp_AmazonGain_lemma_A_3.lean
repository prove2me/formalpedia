-- Prove2me | Theorems.Thm_FBAComp_AmazonGain_lemma_A_3
-- name    : FBAComp.AmazonGain.lemma_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:54:18.62111+00:00
-- url     : https://prove2.me/theorems/389cfa92-8e0e-4499-bb04-094c6c2bb967
-- title:
--   Lemma A.3, p. 35 — unique optimal FBA fee
-- statement:
--   For $\eta\in(0,\alpha)$ and the no-FBA equilibrium as participation benchmark, Amazon's fee problem has exactly one optimal fee $T^*$. If $\widetilde T$ maximizes Amazon's FBA profit without the participation constraint, then
--
--   $$T^*=\min\{\widetilde T,\bar T\}.$$
--
--   This combines the FBA subgame outcome, the seller's participation threshold and Amazon's initial fee choice.
--
--   **Formalization Note.** Feasible fees also require nonnegative seller sales. There is no restriction $T>c$, since the paper's optimization problem (5) omits it.
-- source:
--   Lai, Liu, Xiao & Zhao, “Fulfilled by Amazon”, SSRN preprint 3270958 (PDF of 2021-10-08), p. 35, Lemma A.3 and its proof

import Mathlib
import Definitions.Def_FBAComp_AmazonGain_ClosedForms

namespace FBAComp.AmazonGain

/-- Lemma A.3, p. 35: the participation-constrained FBA fee is unique; its
value is the smaller of the unconstrained maximizer and the seller's threshold. -/
theorem lemma_A_3 (P : Params) (hP : P.Standing) (hI : Interior P)
    (η wN pAN pSN : ℝ) (hη : η ∈ Set.Ioo 0 P.α)
    (hN : IsEqN P η wN pAN pSN) :
    (∃! T : ℝ, ∃ w pA pS : ℝ,
      IsFeeOptimal P η (profitSN P η pAN pSN) T w pA pS) ∧
    (∀ Tfree wfree pAfree pSfree : ℝ,
      IsUnconstrainedFeeOptimal P η Tfree wfree pAfree pSfree →
      ∀ T w pA pS : ℝ,
        IsFeeOptimal P η (profitSN P η pAN pSN) T w pA pS →
        T = min Tfree (Tbar P η)) := by sorry

end FBAComp.AmazonGain
