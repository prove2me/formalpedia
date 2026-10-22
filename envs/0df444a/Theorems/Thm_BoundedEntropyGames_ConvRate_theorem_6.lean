-- Prove2me | Theorems.Thm_BoundedEntropyGames_ConvRate_theorem_6
-- name    : BoundedEntropyGames.ConvRate.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:38.93352+00:00
-- url     : https://prove2.me/theorems/e76a5675-0bb5-4410-8c52-ea74484b2230
-- title:
--   Theorem 6, p. 14 — Alice secures $J_{cav}(H(X|Y))-\mu\big(\frac1n+\frac1{f_n}+\frac{f_n}n+g_n+2^{-\frac12(\frac n{f_n}-1)h_n(\beta g_n-\gamma h_n)}\big)$
-- statement:
--   Consider the $n$-stage repeated zero-sum game with leaked randomness source: finite nonempty action sets $\mathcal A$ (Alice) and $\mathcal B$ (Bob), stage payoff $u_{ab}$ paid by Bob to Alice, and a joint pmf $p_{XY}$ on finite $\mathcal X\times\mathcal Y$. At each stage a fresh pair $(X_t,Y_t)\sim p_{XY}$ is drawn; Alice sees $X_t$, Bob sees $Y_t$, both see past actions, and both use deterministic strategies. Let $\lambda(\sigma^n,\tau^n)$ be Alice's expected average payoff (7) and $J^{(A)}_{cav}$ the upper concave envelope of the entropy-constrained value $J^{(A)}$ of Definition 4.
--
--   There exist real numbers $r>0$, $\beta>0$, $\gamma\ge0$ and $\mu\ge0$ such that for all sequences $(f_n)$ of positive integers and $(g_n)$, $(h_n)$ of reals with $0\le g_n\le r$ and $0\le h_n\le1$, there is a sequence of Alice strategies $(\sigma^n)$ such that for every sequence of Bob strategies $(\tau^n)$ and every $n\ge1$,
--   $$
--   \lambda(\sigma^n,\tau^n)\ge J^{(A)}_{cav}(H(X|Y))-\mu\left(\frac1n+\frac1{f_n}+\frac{f_n}n+g_n+2^{-\frac12\left(\frac n{f_n}-1\right)h_n(\beta g_n-\gamma h_n)}\right).
--   $$
--
--   Since $J^{(A)}_{cav}(H(X|Y))$ bounds the $n$-stage max-min value from above (Theorem 5), choosing $f_n\asymp\sqrt n$ and $g_n\asymp\sqrt{\log n}/n^{1/4}$ shows that the max-min value of the $n$-stage game converges to its long-run limit at rate $\sqrt{\log n}/n^{1/4}$ (Corollary 7).
--
--   **Formalization Note** The constants $r,\beta,\gamma,\mu$ are chosen after the game ($u$, $p_{XY}$) and before the sequences, the strategies and $n$. "$f_n\in\mathbb N$" and "$n\in\mathbb N$" are read as $f_n\ge1$ and $n\ge1$, because (10) divides by both. Stages are 0-based in Lean. Strategies are deterministic, Alice's stage-$t$ action reads only the past action pairs and $X_1,\dots,X_t$, Bob's only the past action pairs and $Y_1,\dots,Y_t$, and Bob ranges over all such strategies. The power of $2$ is a real power.
-- source:
--   Valizadeh, Gohari, Playing Games with Bounded Entropy: Convergence Rate and Approximate Equilibria, arXiv:1902.03676v1, p. 14, Theorem 6, (10)

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting

namespace BoundedEntropyGames.ConvRate

/-- Theorem 6, p. 14: in the `n`-stage repeated game with leaked randomness source, Alice
secures `J_cav(H(X|Y))` up to the error term of (10). Stages are 0-based (`Fin n`); `n ∈ ℕ`
and `f_n ∈ ℕ` are read as `1 ≤ n` and `1 ≤ f_n` because (10) divides by both. -/
theorem theorem_6 {𝒜 ℬ 𝒳 𝒴 : Type*} [Fintype 𝒜] [DecidableEq 𝒜] [Nonempty 𝒜]
    [Fintype ℬ] [DecidableEq ℬ] [Nonempty ℬ] [Fintype 𝒳] [DecidableEq 𝒳]
    [Fintype 𝒴] [DecidableEq 𝒴]
    (u : 𝒜 → ℬ → ℝ) (pXY : 𝒳 × 𝒴 → ℝ) (hp : IsPMF pXY) :
    ∃ r > (0 : ℝ), ∃ β > (0 : ℝ), ∃ γ ≥ (0 : ℝ), ∃ μ ≥ (0 : ℝ),
      ∀ (f : ℕ → ℕ) (g h : ℕ → ℝ), (∀ n, 1 ≤ f n) → (∀ n, 0 ≤ g n ∧ g n ≤ r) →
        (∀ n, 0 ≤ h n ∧ h n ≤ 1) →
        ∃ σ : (n : ℕ) → AliceStrategy 𝒜 ℬ 𝒳 n,
          ∀ (τ : (n : ℕ) → BobStrategy 𝒜 ℬ 𝒴 n) (n : ℕ), 1 ≤ n →
            Jcav u (condEntropy pXY) -
                μ * (1 / (n : ℝ) + 1 / (f n : ℝ) + (f n : ℝ) / n + g n +
                  (2 : ℝ) ^ (-(1 / 2) * ((n : ℝ) / f n - 1) * h n * (β * g n - γ * h n)))
              ≤ payoff u pXY (σ n) (τ n) := by sorry

end BoundedEntropyGames.ConvRate
