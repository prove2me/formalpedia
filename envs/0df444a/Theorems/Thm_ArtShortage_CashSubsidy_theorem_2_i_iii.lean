-- Prove2me | Theorems.Thm_ArtShortage_CashSubsidy_theorem_2_i_iii
-- name    : ArtShortage.CashSubsidy.theorem_2_i_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:23:44.543948+00:00
-- url     : https://prove2.me/theorems/0e240fb9-622a-4e48-b50d-c6a3aa54d520
-- title:
--   Theorem 2(i)–(iii), p. 17 — the trader's CS Period-1 quantity: 1/2 − g/8 below t1, then the roots of two first-order conditions
-- statement:
--   Fix $0<g<4$ and $1+g<\lambda$, and let $\mathrm{EqQ1}(b)$ be the set of equilibrium Period-1 quantities of the cash-subsidy game with government budget $b$. For every $b\ge0$ this set is nonempty. Moreover, there is a threshold $t_1$ with $0<t_1<(8+4g+g^2)/32$ such that:
--
--   1. if $0\le b<t_1$: $\mathrm{EqQ1}(b)=\{1/2-g/8\}$;
--   2. at $b=t_1$, some $q_1\in\mathrm{EqQ1}(t_1)$ solves $F_2(b,q_1)=0$; and if $t_1<b<(8+4g+g^2)/32$, every $q_1\in\mathrm{EqQ1}(b)$ lies in $[0,1]$ and solves $F_2(b,q_1)=0$, where
--   $$F_2(b,q)=1-2q+\frac{g^2(-1+q)-g\Big(1+6b+\sqrt{(1+g(1-q))(1+g+12b-gq)}\Big)}{9\sqrt{(-1+g(-1+q))(-1-12b+g(-1+q))}};$$
--   3. if $(8+4g+g^2)/32\le b<(4+2g+g^2)/4$: every $q_1\in\mathrm{EqQ1}(b)$ lies in $[0,1]$ and solves
--   $$1-2q_1-\frac{bg}{2\sqrt{b(1+g(1-q_1))}}=0 .$$
--
--   These are the first-order conditions of the trader's Period-1 problem at the second mode of his bimodal objective, once the government's subsidy reaches the subsidized consumers.
--
--   **Formalization Note** The printed radical in the numerator of (ii) reads $\sqrt{1+g(1-q_1)(1+g+12b-gq_1)}$, which is missing the parentheses around $1+g(1-q_1)$. It is read as the product $(1+g(1-q_1))(1+g+12b-gq_1)$, which matches Theorem 1(ii) and the denominator. $t_1$ (Lemma O.1, not in the paper) is existential and is pinned by clause 1 together with the jump at $t_1$. At $b=t_1$ the two modes tie, so the statement there is existential. Nonemptiness of $\mathrm{EqQ1}$ is asserted, because the page presupposes that "the optimal quantity" exists.
-- source:
--   Levi, Singhvi & Zheng, Artificial Shortage in Agricultural Supply Chains, SSRN 3332493 (version of 2021-04-14; MSOM forthcoming), p. 17, Theorem 2 (i)–(iii)

import Mathlib
import Definitions.Def_ArtShortage_CashSubsidy_Model

namespace ArtShortage.CashSubsidy

theorem theorem_2_i_iii (g lam : ℝ) (hS : Standing g lam) :
    let F2 : ℝ → ℝ → ℝ := fun b q =>
      1 - 2 * q + (g^2 * (-1 + q) - g * (1 + 6 * b +
          Real.sqrt ((1 + g * (1 - q)) * (1 + g + 12 * b - g * q)))) /
        (9 * Real.sqrt ((-1 + g * (-1 + q)) * (-1 - 12 * b + g * (-1 + q))))
    let F3 : ℝ → ℝ → ℝ := fun b q =>
      1 - 2 * q - b * g / (2 * Real.sqrt (b * (1 + g * (1 - q))))
    (∀ b, 0 ≤ b → (EqQ1 g lam b).Nonempty) ∧
    ∃ t1 : ℝ, 0 < t1 ∧ t1 < (8 + 4 * g + g^2) / 32 ∧
      -- (i)
      (∀ b, 0 ≤ b → b < t1 → EqQ1 g lam b = {1/2 - g/8}) ∧
      -- (ii)
      (∃ q ∈ EqQ1 g lam t1, F2 t1 q = 0) ∧
      (∀ b, t1 < b → b < (8 + 4 * g + g^2) / 32 → ∀ q ∈ EqQ1 g lam b,
        q ∈ Set.Icc (0:ℝ) 1 ∧ F2 b q = 0) ∧
      -- (iii)
      (∀ b, (8 + 4 * g + g^2) / 32 ≤ b → b < (4 + 2 * g + g^2) / 4 → ∀ q ∈ EqQ1 g lam b,
        q ∈ Set.Icc (0:ℝ) 1 ∧ F3 b q = 0) := by sorry

end ArtShortage.CashSubsidy
