-- Prove2me | Theorems.Thm_BoundedEntropyGames_ConvRate_lemma_14
-- name    : BoundedEntropyGames.ConvRate.lemma_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:16:40.371416+00:00
-- url     : https://prove2.me/theorems/34059c24-5c4d-4e73-905c-6cb826fcd43c
-- title:
--   Lemma 14, p. 18 — a random map with i.i.d. $p_A$ values simulates $A$ from $X$ within $2^{-(1-1/\alpha)(H_\alpha(X|Y)-H_{1/\alpha}(A)+2)}$
-- statement:
--   Let $(X,Y)$ have joint pmf $p_{XY}$ on finite $\mathcal X\times\mathcal Y$, let $p_A$ be a pmf on finite $\mathcal A$, and let $F:\mathcal X\to\mathcal A$ be the random mapping whose values $F(x)$ are i.i.d. with law $p_A$, so that $p_F(f)=\prod_xp_A(f(x))$. For a map $f$, let $p_{f(X)Y}$ be the joint pmf of $(f(X),Y)$. Then:
--
--   1. for every $\alpha\in[1,2]$,
--   $$
--   \sum_{f}p_F(f)\,\|p_{f(X)Y}-p_Ap_Y\|_{TV}\le 2^{-(1-\frac1\alpha)\left(H_\alpha(X|Y)-H_{1/\alpha}(A)+2\right)};
--   $$
--   2. there is a single deterministic map $f:\mathcal X\to\mathcal A$ such that $\|p_{f(X)Y}-p_Ap_Y\|_{TV}\le 2^{-(1-\frac1\alpha)\left(H_\alpha(X|Y)-H_{1/\alpha}(A)+2\right)}$ for all $\alpha\in[1,2]$ simultaneously.
--
--   Part 1 is equivalent to the paper's bound by the minimum over $\alpha\in[1,2]$ (14); part 2 is (15). The lemma is the simulation tool of the paper: a deterministic function of Alice's source produces an action whose joint law with Bob's observation is close to independent with law $p_A$.
--
--   **Formalization Note** At $\alpha=1$ the factor $1-1/\alpha$ vanishes and the bound equals $1$; the Rényi entropies there are junk values multiplied by $0$. For $\alpha\in(1,2]$, $H_{1/\alpha}$ is the Rényi entropy of order $1/\alpha\in[1/2,1)$.
-- source:
--   Valizadeh, Gohari, Playing Games with Bounded Entropy: Convergence Rate and Approximate Equilibria, arXiv:1902.03676v1, p. 18, Lemma 14, (14)–(15)

import Mathlib
import Definitions.Def_BoundedEntropyGames_ConvRate_Setting
import Definitions.Def_BoundedEntropyGames_ConvRate_Proof

namespace BoundedEntropyGames.ConvRate

/-- Lemma 14, p. 18: the random mapping `F` with i.i.d. `p_A` values simulates `A` from `X`
on average within `2^{-(1-1/α)(H_α(X|Y) - H_{1/α}(A) + 2)}` for every `α ∈ [1, 2]` (14), and
some deterministic `f` does so for all `α ∈ [1, 2]` simultaneously (15). -/
theorem lemma_14 {𝒳 𝒴 𝒜 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [Fintype 𝒴]
    [Fintype 𝒜] [DecidableEq 𝒜]
    (pXY : 𝒳 × 𝒴 → ℝ) (hpXY : IsPMF pXY) (pA : 𝒜 → ℝ) (hpA : IsPMF pA) :
    (∀ α ∈ Set.Icc (1 : ℝ) 2,
      ∑ f : 𝒳 → 𝒜, pF pA f * tv (pfXY pXY f) (fun z => pA z.1 * marginalY pXY z.2)
        ≤ (2 : ℝ) ^ (-(1 - 1 / α) * (condRenyi α pXY - renyi (1 / α) pA + 2))) ∧
    ∃ f : 𝒳 → 𝒜, ∀ α ∈ Set.Icc (1 : ℝ) 2,
      tv (pfXY pXY f) (fun z => pA z.1 * marginalY pXY z.2)
        ≤ (2 : ℝ) ^ (-(1 - 1 / α) * (condRenyi α pXY - renyi (1 / α) pA + 2)) := by sorry

end BoundedEntropyGames.ConvRate
