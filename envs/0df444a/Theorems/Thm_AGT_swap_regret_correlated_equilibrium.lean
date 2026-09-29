-- Prove2me | Theorems.Thm_AGT_swap_regret_correlated_equilibrium
-- name    : AGT.swap_regret_correlated_equilibrium
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T03:33:16.442704+00:00
-- url     : https://prove2.me/theorems/a3d5594a-9ac1-4862-92c8-f7afc878440a
-- title:
--   Low swap regret play is an approximate correlated equilibrium
-- statement:
--   Play with low swap regret is, in the aggregate, an approximate correlated equilibrium (Theorem 4.12 of *Algorithmic Game Theory*). Let a finite game with cost functions $c_i$ be played for $T \ge 1$ steps, the players independently drawing from mixed profiles $\sigma^0,\dots,\sigma^{T-1}$. Assume every player's swap regret over these steps is at most $R$: for each player $i$ and every switching rule $F : S_i \to S_i$, the cumulative expected cost of the actual play exceeds that of the $F$-modified play by at most $R$. Then the empirical distribution of joint play,
--   $$Q(s) \;=\; \frac1T \sum_{t<T} \prod_j \sigma^t_j(s_j),$$
--   is an $(R/T)$-correlated equilibrium in the sense of Definition 4.11.
--
--   *A note on the rendering.* The hypothesis $T \ge 1$ is required — at $T = 0$ the empirical distribution is identically zero and no distribution at all. Costs are not assumed $[0,1]$-bounded: the book scales losses into $[0,1]$ globally, but the averaging argument is scale-free, so the formal statement omits the restriction and is the stronger claim. $R$ may be any real; a negative $R$ only strengthens the hypothesis.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 4.4.4, Theorem 4.12, pp. 91-92

import Definitions.Def_agt_regret

namespace AGT

/-- **Theorem 4.12 of *Algorithmic Game Theory***: low swap regret play is an
approximate correlated equilibrium.  Suppose the players of a finite game
play mixed profiles `σ 0, σ 1, …` (independently at each step), and over the
first `T ≥ 1` steps every player's swap regret is at most `R`: switching
their own coordinate by any fixed rule `F` would have saved at most `R` in
cumulative expected cost.  Then the empirical distribution of joint play —
the average `Q(s) = (1/T) ∑_{t<T} ∏_j σⱼᵗ(sⱼ)` — is an `(R/T)`-correlated
equilibrium.

The hypothesis `0 < T` is required: at `T = 0` the empirical distribution is
identically zero and no lottery.  Costs need not be `[0,1]`-bounded; the
averaging argument is scale-free. -/
theorem swap_regret_correlated_equilibrium {ι : Type*} [Fintype ι]
    [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
    (cost : ι → (∀ i, S i) → ℝ) (T : ℕ) (hT : 0 < T)
    (σ : ℕ → ∀ i, S i → ℝ) (hσ : ∀ t, t < T → IsMixedProfile (σ t)) (R : ℝ)
    (hswap : ∀ i (F : S i → S i),
      ∑ t ∈ Finset.range T, ∑ s, profileProb (σ t) s * cost i s ≤
        (∑ t ∈ Finset.range T, ∑ s,
          profileProb (σ t) s * cost i (Function.update s i (F (s i)))) + R) :
    IsCorrelatedEquilibrium (R / T) cost
      (fun s => (∑ t ∈ Finset.range T, profileProb (σ t) s) / T) := by
  sorry

end AGT
