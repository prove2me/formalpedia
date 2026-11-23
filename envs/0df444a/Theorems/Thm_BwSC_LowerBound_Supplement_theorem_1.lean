-- Prove2me | Theorems.Thm_BwSC_LowerBound_Supplement_theorem_1
-- name    : BwSC.LowerBound.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T09:44:05.503609+00:00
-- url     : https://prove2.me/theorems/5c4c7aae-27ee-4b4e-9b22-4d995ff5b168
-- title:
--   Theorem 1 (corrected boundary conventions) — AdaLS admissibility and full worst-case upper bound
-- statement:
--   Let $K\ge1$, $S\in\mathbb N$, $T\ge K$, and let $\pi$ be the full AdaLS policy of Algorithm 2 with $\lambda=1/2$. Such a policy exists on the canonical history space. It belongs to $\Pi_S$: under every normalized, integrable, centered 1-sub-Gaussian environment with mean spread at most one it makes at most $S$ switches almost surely. One absolute $C\ge0$, chosen before $K,S,T$, the policy and the environment, gives
--   $$R^\pi_\nu(K,T)\le C(\log T)^2\max\left\{\frac{(K-r)^{2-1/(2-2^{-q})}}K T^{1/(2-2^{-q})},\ K^{1-1/(2-2^{-q-1})}T^{1/(2-2^{-q-1})}\right\}$$
--   for every such environment when $K>1$. For $K=1$ the conclusion is zero regret. Here $q=q(S,K)$ and $r=r(S,K)$ are the published phase indices, including $q(0,K)=0$ and $r(0,K)=-1$.
--
--   This uniform per-environment bound is the source's worst-case regret bound and is a companion to the existing lower-bound goal.
--
--   **Formalization Note** Natural logarithms are used. No Gaussian restriction, clean-event hypothesis or large-horizon cutoff is added. The algorithm specification and all boundary conventions are documented in the AdaLS definition. The statement asserts existence and covers every policy realizing the specified kernels.
--
--   Differences from the source:
--   - encoding: The source specifies randomized Algorithms 2 and 6 procedurally. → A full deterministic replay per initial seed fixes their canonical conditional action laws; policy existence is part of the theorem conclusion.; reason: This separates operational behavior from its guarantees and makes realization nonvacuous.
--   - correction: The algorithms divide by K−1 at K=1 and do not define zero-sample confidence bounds, negative or empty-loop counts, or plays beyond T. → The sole arm is played at K=1 with zero regret; no-sample means are −∞ and confidence intervals are full; empty loops do nothing, counts are nonnegative and plays are clipped at T.; reason: Complete all finite inputs without excluding any source case; p. 14 supplies the unobserved mean, p. 45 treats small horizons by the trivial regret bound, and a one-arm instance has no regret.
--   - reading: Arbitrary iteration choices and empirical-maximizer ties are left unspecified. → Increasing labels are used, with the required previous-arm priority; final ties prefer the previous arm, then the least label; S=0 keeps a0.; reason: These are causal permissible choices; at S=0 all empirical means are −∞ and retaining a0 gives the stated no-switch behavior.
-- source:
--   Simchi-Levi & Xu, arXiv:1905.10825v4, p. 19, Theorem 1; Algorithm 2 p. 18, proof Appendix F pp. 45–52

import Mathlib
import Definitions.Def_BwSC_LowerBound_Supplement_AdaLS

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace BwSC.LowerBound.Supplement

theorem theorem_1 :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K S T : ℕ) (hK : 0 < K), K ≤ T →
      (∃ π : BanditPolicy K, IsAdaLS hK S T π) ∧
      ∀ π : BanditPolicy K, IsAdaLS hK S T π →
        IsAdmissiblePolicy S T π ∧
        ∀ ν : StochasticBandit K, AdmissibleEnvironment ν →
          banditRegret ν π T ≤
            if K = 1 then 0 else
              C * (Real.log T) ^ 2 * max (rateA K S T) (rateB K S T) := by sorry

end BwSC.LowerBound.Supplement
