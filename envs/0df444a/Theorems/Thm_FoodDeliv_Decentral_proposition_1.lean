-- Prove2me | Theorems.Thm_FoodDeliv_Decentral_proposition_1
-- name    : FoodDeliv.Decentral.proposition_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:21.353265+00:00
-- url     : https://prove2.me/theorems/9bf8e3f4-9394-44fe-96a7-6d4873ff0049
-- title:
--   Proposition 1 (p. 8) — equilibrium in the decentralized system: delivery-irrelevant vs delivery-only regime
-- statement:
--   Let $R,\mu,c,\Lambda_0$ satisfy $\mu>0$, $c>0$, $c<R\mu$ and $\Lambda_0\ge\mu$. There is $\phi_1$ such that for every $\phi\in[0,c)$ there are $\lambda_1\in(0,\mu)$ and, for every $\Lambda_1\in(0,\mu)$, a subgame-perfect equilibrium of the food-delivery game with parameters $(R,\mu,c,\phi,\Lambda_0,\Lambda_1)$ whose outcome $p^*,\pi^*,S^*,\lambda^*_D,\lambda^*_W$ (as functions of $\Lambda_1$) satisfies the following. Let $I=(0,\mu)$ if $\phi>\phi_1$ and $I=(0,\lambda_1]$ if $\phi\le\phi_1$.
--
--   1. On $I$, $p^*$ and $\lambda^*_D+\lambda^*_W$ are constant, while $\pi^*$, $S^*$, $\lambda^*_D$ and $-\lambda^*_W$ are weakly increasing in $\Lambda_1$.
--   2. If $\phi\le\phi_1$:
--   $$p^*(a)<p^*(b)\ \ (a\in(0,\lambda_1],\ b\in(\lambda_1,\mu)),\qquad \pi^*(\lambda_1)>\lim_{\Lambda_1\searrow\lambda_1}\pi^*(\Lambda_1),\qquad S^*(\lambda_1)>\lim_{\Lambda_1\searrow\lambda_1}S^*(\Lambda_1),$$
--   both limits existing.
--   3. If $\phi<c/(2\sqrt{R\mu/c}-1)$, then $c/(2\sqrt{R\mu/c}-1)\le\phi_1$, the limit $L=\lim_{\Lambda_1\nearrow\mu}(\lambda^*_D+\lambda^*_W)$ exists, and $\lambda^*_D+\lambda^*_W<L$ on $(0,\lambda_1]$.
--
--   In words: if delivery is inconvenient or tech-savvy customers are few, the restaurant ignores the platform and more tech-savvy customers only shift its customer mix; otherwise, at a critical mass $\lambda_1$, the restaurant switches to a delivery-only regime with a higher price, the platform's profit and welfare drop, and when delivery is convenient enough, demand eventually exceeds its level before delivery.
--
--   **Formalization Note** The equilibrium is defined by optimality conditions (customers' equilibrium with the p. 7 tie rule, the platform's best response over $\theta\ge0$, the restaurant's optimum over $p\ge0$), never by the paper's tables. $S^*$ includes the customers' surplus. "$p^*$" is read existentially: there is an SPE at every $\Lambda_1\in(0,\mu)$, including $\lambda_1$ itself, with these properties; at $\Lambda_1=\lambda_1$, and when $\phi=\phi_1$ on part of $(\lambda_1,\mu)$, the restaurant has two optimal prices (findings F1, F2), and the universal reading is false there. "$\pi^*|_{\Lambda_1\le\lambda_1}>\pi^*|_{\Lambda_1\searrow\lambda_1}$" is read as the value at $\lambda_1$ against the right limit, which the proof compares (Online Appendix p. 27); "$\lambda^*_D+\lambda^*_W|_{\Lambda_1\nearrow\mu}$" is the left limit at $\mu$; limits are asserted to exist. In "if $\phi<c/(2\sqrt{R\mu/c}-1)\le\phi_1$" the part "$\le\phi_1$" is a conclusion. $c<R\mu$ is used by the paper's proofs without being stated (finding F4); $\Lambda_1<\mu$ is the paper's focus (Online Appendix p. 7). $\phi=0$ is included, as in the paper.
-- source:
--   Chen, Hu & Wang, Food Delivery Service and Restaurant: Friend or Foe?, SSRN 3469971 (author version of Management Sci. DOI 10.1287/mnsc.2021.4245), p. 8, Proposition 1

import Mathlib
import Definitions.Def_FoodDeliv_Decentral_Model

open Filter Topology

namespace FoodDeliv.Decentral

/-- Proposition 1 (Equilibrium in Decentralized System), p. 8, its "Formally, …" sentence:
there exist `ϕ1` and, for each `ϕ ∈ [0, c)`, a threshold `λ1 ∈ (0, μ)` (`l1` in Lean) and a subgame-perfect
equilibrium `E Λ1` of the game with tech-savvy arrival rate `Λ1`, for every `Λ1 ∈ (0, μ)`, such
that, writing `p*, π*, S*, λ*_D, λ*_W` for its outcome:
1. if `ϕ > ϕ1`, on `(0, μ)`, and if `ϕ ≤ ϕ1`, on `(0, λ1]`: `p*` and `λ*_D + λ*_W` are constant,
   and `π*`, `S*`, `λ*_D`, `-λ*_W` are weakly increasing in `Λ1`;
2. if `ϕ ≤ ϕ1`: `p*` on `(0, λ1]` is below `p*` on `(λ1, μ)`, and `π*`, `S*` at `λ1` exceed
   their right limits at `λ1`;
3. if `ϕ < c / (2√(Rμ/c) - 1)`, then `c / (2√(Rμ/c) - 1) ≤ ϕ1` and `λ*_D + λ*_W` on `(0, λ1]`
   is below its left limit at `μ`. -/
theorem proposition_1 (R μ c Λ0 : ℝ) (hμ : 0 < μ) (hc : 0 < c) (hcR : c < R * μ)
    (hΛ0 : μ ≤ Λ0) :
    ∃ ϕ1 : ℝ, ∀ ϕ : ℝ, 0 ≤ ϕ → ϕ < c →
    ∃ l1 : ℝ, 0 < l1 ∧ l1 < μ ∧
    ∃ E : ℝ → Strategy,
      (∀ Λ1 ∈ Set.Ioo 0 μ, IsSPE ⟨R, μ, c, ϕ, Λ0, Λ1⟩ (E Λ1)) ∧
      let I : Set ℝ := if ϕ1 < ϕ then Set.Ioo 0 μ else Set.Ioc 0 l1
      -- (i) / (ii)
      ((∀ a ∈ I, ∀ b ∈ I, (E a).pStar = (E b).pStar) ∧
        (∀ a ∈ I, ∀ b ∈ I,
          (E a).lamDStar + (E a).lamWStar = (E b).lamDStar + (E b).lamWStar) ∧
        MonotoneOn (fun Λ1 => (E Λ1).platProfitStar) I ∧
        MonotoneOn (fun Λ1 => (E Λ1).welfareStar ⟨R, μ, c, ϕ, Λ0, Λ1⟩) I ∧
        MonotoneOn (fun Λ1 => (E Λ1).lamDStar) I ∧
        MonotoneOn (fun Λ1 => -(E Λ1).lamWStar) I) ∧
      -- otherwise
      (ϕ ≤ ϕ1 →
        (∀ a ∈ Set.Ioc 0 l1, ∀ b ∈ Set.Ioo l1 μ, (E a).pStar < (E b).pStar) ∧
        (∃ L : ℝ, Tendsto (fun Λ1 => (E Λ1).platProfitStar) (𝓝[>] l1) (𝓝 L) ∧
          L < (E l1).platProfitStar) ∧
        (∃ L : ℝ, Tendsto (fun Λ1 => (E Λ1).welfareStar ⟨R, μ, c, ϕ, Λ0, Λ1⟩) (𝓝[>] l1) (𝓝 L) ∧
          L < (E l1).welfareStar ⟨R, μ, c, ϕ, Λ0, l1⟩)) ∧
      -- furthermore
      (ϕ < c / (2 * Real.sqrt (R * μ / c) - 1) →
        c / (2 * Real.sqrt (R * μ / c) - 1) ≤ ϕ1 ∧
        ∃ L : ℝ, Tendsto (fun Λ1 => (E Λ1).lamDStar + (E Λ1).lamWStar) (𝓝[<] μ) (𝓝 L) ∧
          ∀ a ∈ Set.Ioc 0 l1, (E a).lamDStar + (E a).lamWStar < L) := by sorry

end FoodDeliv.Decentral
