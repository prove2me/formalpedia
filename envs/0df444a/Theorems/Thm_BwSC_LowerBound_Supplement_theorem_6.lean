-- Prove2me | Theorems.Thm_BwSC_LowerBound_Supplement_theorem_6
-- name    : BwSC.LowerBound.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:44:53.293365+00:00
-- url     : https://prove2.me/theorems/ac0ce56e-a797-4edd-866f-ee948b6dc33c
-- title:
--   Theorem 6 (corrected boundary conventions) — AdaLS2 full printed instance-dependent upper bound
-- statement:
--   Let $K\ge1$, $S\in\mathbb N$ and $T\ge K$. The full AdaLS2 policy of Algorithm 6 exists on canonical histories. Let $\nu$ be any normalized, integrable, centered 1-sub-Gaussian environment with mean spread at most one. If $K>1$, suppose its best arm is unique, and let $\Delta=\min_{j\ne k^*}(\mu_{k^*}-\mu_j)>0$ be its actual gap. There is one absolute $C\ge0$, chosen before all these data, such that
--   $$R^\pi_\nu(K,T)\le C(\log K\log T)\max\left\{\frac{(K-r)^{2-1/(q+1)}}K\frac{T^{1/(q+1)}}\Delta,\ K^{1-1/(q+1)}\frac{T^{1/(q+1)}}\Delta\right\}.$$
--   Here $q=q(S,K)$ and $r=r(S,K)$. For $K=1$, regret is zero without requiring another arm or a positive gap.
--
--   This companion theorem gives the printed instance-dependent upper bound. Both occurrences of the second rate's denominator are $q+1$, as printed, even though Algorithm 6's second grid and Theorem 7 use $q+2$.
--
--   **Formalization Note** The positive-gap premise comes from Appendix A, p. 38. No uniform lower bound on the gap and no distribution restriction beyond the source model is imposed. The statement includes existence and covers every policy realizing the full AdaLS2 kernel specification.
--
--   Differences from the source:
--   - encoding: The source specifies randomized Algorithms 2 and 6 procedurally. → A full deterministic replay per initial seed fixes their canonical conditional action laws; policy existence is part of the theorem conclusion.; reason: This separates operational behavior from its guarantees and makes realization nonvacuous.
--   - correction: The algorithms divide by K−1 at K=1 and do not define zero-sample confidence bounds, negative or empty-loop counts, or plays beyond T. → The sole arm is played at K=1 with zero regret; no-sample means are −∞ and confidence intervals are full; empty loops do nothing, counts are nonnegative and plays are clipped at T.; reason: Complete all finite inputs without excluding any source case; p. 14 supplies the unobserved mean, p. 45 treats small horizons by the trivial regret bound, and a one-arm instance has no regret.
--   - reading: Arbitrary iteration choices and empirical-maximizer ties are left unspecified. → Increasing labels are used, with the required previous-arm priority; final ties prefer the previous arm, then the least label; S=0 keeps a0.; reason: These are causal permissible choices; at S=0 all empirical means are −∞ and retaining a0 gives the stated no-switch behavior.
--   - reading: Appendix A defines Δ>0 for a unique best arm; the theorem sentence says all D. → At K>1 the bound is conditioned on the environment’s computed positive gap; K=1 instead states zero regret.; reason: This includes the governing assumption on p. 38 without adding a positive gap lower bound.
--   - correction: Algorithm 6 refers to Lines 1–18 of Algorithm 2. → All actual Lines 1–16 are used.; reason: Algorithm 2 on p. 18 ends at Line 16; no additional algorithm lines exist.
-- source:
--   Simchi-Levi & Xu, arXiv:1905.10825v4, p. 39, Theorem 6; Appendix A pp. 38–39; Algorithm 6 p. 38, proof instruction to Appendix F

import Mathlib
import Definitions.Def_BwSC_LowerBound_Supplement_AdaLS2
import Definitions.Def_BwSC_LowerBound_Supplement_Gap

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace BwSC.LowerBound.Supplement

theorem theorem_6 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K S T : ℕ) (hK : 0 < K), K ≤ T →
      (∃ π : BanditPolicy K, IsAdaLS2 hK S T π) ∧
      ∀ π : BanditPolicy K, IsAdaLS2 hK S T π →
        ∀ ν : StochasticBandit K, AdmissibleEnvironment ν →
          (K = 1 → banditRegret ν π T = 0) ∧
          (1 < K → 0 < sourceGap ν →
            banditRegret ν π T ≤ C * (Real.log K * Real.log T) *
              max (gapRateA K S T / sourceGap ν) (gapRateBUpper K S T / sourceGap ν)) := by sorry

end BwSC.LowerBound.Supplement
