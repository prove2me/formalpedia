-- Prove2me | Theorems.Thm_BwSC_LowerBound_Supplement_theorem_7
-- name    : BwSC.LowerBound.Supplement.theorem_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T09:45:35.611337+00:00
-- url     : https://prove2.me/theorems/33ac8c1d-93c9-45cf-aa11-08663f9c4a02
-- title:
--   Theorem 7 — full gap-weighted minimax lower bound
-- statement:
--   Let $K>1$, $S\in\mathbb N$, $T\ge2K$ and let $\pi\in\Pi_S$, meaning that its switching budget holds almost surely under every normalized, integrable, centered 1-sub-Gaussian environment with mean spread at most one. For each environment $\nu$ with a unique best arm let $\Delta(\nu)$ be its actual positive best-versus-runner-up gap; tied optima contribute zero. There is one absolute $C>0$, chosen before $K,S,T,\pi$, such that
--   $$\sup_{\nu\in\mathcal E_K}\Delta(\nu)R^\pi_\nu(K,T)\ge\frac C{\log T}\max\left\{\frac{(K-r)^{2-1/(q+1)}}K T^{1/(q+1)},\ K^{1-1/(q+2)}T^{1/(q+2)}\right\}.$$
--   Here $q=q(S,K)$ and $r=r(S,K)$ use the published zero-budget convention, and $\mathcal E_K$ is the full admissible environment class.
--
--   This is the companion gap-weighted minimax lower bound. The gap multiplies the regret on the left; neither rate on the right is divided by a gap.
--
--   **Formalization Note** The supremum is taken in the extended reals over environments and their own gaps, avoiding a free unrelated $\mathcal D$ or a conditional-completeness default. All source horizons and budgets are retained.
--
--   Differences from the source:
--   - reading: The printed left side is sup over Δ∈[0,1] of Δ R_D^π, without separately binding D. → The supremum ranges over admissible environments ν with their own actual gap Δ(ν); ties have gap zero.; reason: Appendix A defines Δ=Δ(D) and gives a minimax interpretation, so D cannot be unrelated to the supremum variable.
--   - encoding: The source uses an ordinary supremum of real regrets. → An EReal supremum is used and the finite lower bound is coerced into EReal.; reason: This has no empty or unbounded real-supremum default and states the same inequality on the full environment class.
-- source:
--   Simchi-Levi & Xu, arXiv:1905.10825v4, p. 39, Theorem 7; Appendix A pp. 38–39; proof instruction to Appendix J

import Mathlib
import Definitions.Def_BwSC_LowerBound_Supplement_Gap

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace BwSC.LowerBound.Supplement

theorem theorem_7 :
    ∃ C : ℝ, 0 < C ∧ ∀ (K S T : ℕ), 1 < K → 2 * K ≤ T →
      ∀ π : BanditPolicy K, IsAdmissiblePolicy S T π →
        ((C / Real.log T * max (gapRateA K S T) (gapRateBLower K S T) : ℝ) : EReal) ≤
          gapWeightedWorstRegret π T := by sorry

end BwSC.LowerBound.Supplement
