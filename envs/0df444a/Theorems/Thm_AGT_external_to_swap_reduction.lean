-- Prove2me | Theorems.Thm_AGT_external_to_swap_reduction
-- name    : AGT.external_to_swap_reduction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T03:33:02.361433+00:00
-- url     : https://prove2.me/theorems/49160d33-2132-473a-a8ba-92da3fe29693
-- title:
--   Reduction from external to swap regret (Blum-Mansour)
-- statement:
--   Any online algorithm with small external regret can be converted, black-box, into one with small swap regret — the Blum–Mansour reduction (Theorem 4.15 of *Algorithmic Game Theory*). Suppose the online algorithm $A$ on $N = n+1$ actions plays genuine probability distributions and guarantees, at horizon $T$, external regret at most $R$ against every $[0,1]$-valued loss sequence: $L^T_A \le L^T_k + R$ for every action $k$. Then there exists an online algorithm $H$ — the master procedure assembled from $N$ copies of $A$ — playing genuine distributions, such that against every $[0,1]$-valued loss sequence and every modification rule $F : \{1,\dots,N\} \to \{1,\dots,N\}$,
--   $$L^T_H \;\le\; L^T_{H,F} + N\,R,$$
--   i.e. the swap regret of $H$ at horizon $T$ is at most $N R$.
--
--   *A note on the construction and the quantifiers.* $H$ is chosen after $A$, $R$, $T$ but before the loss sequence and the rule $F$ — the witness must work uniformly against every adversary; nothing is chosen with hindsight. The intended witness runs copy $i$ of $A$ on the true losses scaled by $H$'s own probability of action $i$, and plays the stationary distribution of the stochastic matrix assembled from the copies' outputs; the existence of that fixed point is the existence of a stationary distribution of a finite Markov chain — available on this platform as the goal of *Markov Chains and Mixing Times I*, or provable directly.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 4.5, Theorem 4.15, pp. 92-94

import Definitions.Def_agt_regret

namespace AGT

/-- **Theorem 4.15 of *Algorithmic Game Theory* (Blum–Mansour)**: the generic
reduction from external to swap regret.  If an online algorithm `A` on
`n + 1` actions plays genuine distributions and guarantees external regret
at most `R` at horizon `T` against every `[0,1]`-valued loss sequence, then
there is an online algorithm `H` (the master procedure built from `n + 1`
copies of `A`) that plays genuine distributions and whose swap regret at
horizon `T` is at most `(n + 1) · R`: for every `[0,1]`-valued loss sequence
and every modification rule `F`, `L_H ≤ L_{H,F} + (n+1) R`. -/
theorem external_to_swap_reduction {n : ℕ} (T : ℕ) (R : ℝ)
    (A : OnlineAlgorithm (n + 1)) (hAdist : ∀ h, IsLottery (A h))
    (hA : ∀ ℓ : ℕ → Fin (n + 1) → ℝ, (∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) →
      ∀ k, algLoss A ℓ T ≤ actionLoss ℓ k T + R) :
    ∃ H : OnlineAlgorithm (n + 1), (∀ h, IsLottery (H h)) ∧
      ∀ ℓ : ℕ → Fin (n + 1) → ℝ, (∀ t i, ℓ t i ∈ Set.Icc (0 : ℝ) 1) →
        ∀ F : Fin (n + 1) → Fin (n + 1),
          algLoss H ℓ T ≤ swapLoss H ℓ F T + (n + 1) * R := by
  sorry

end AGT
