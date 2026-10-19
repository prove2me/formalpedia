-- Prove2me | Theorems.Thm_ArtShortage_CashSubsidy_proposition_3
-- name    : ArtShortage.CashSubsidy.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:23:43.654579+00:00
-- url     : https://prove2.me/theorems/4ed19a92-7556-42f7-be84-11d72fd060c0
-- title:
--   Proposition 3, p. 22 — cash subsidy leaves q1 unchanged for b < t1, raises it up to (8+4g+g²)/32, lowers it below q1_φ beyond, and q1 is non-increasing in b above t1
-- statement:
--   Fix $0<g<4$ and $1+g<\lambda$. Let $q^1_\phi=1/2-g/8$ be the no-intervention Period-1 quantity (Proposition 1). Let $\mathrm{EqQ1}(b)$ be the set of equilibrium Period-1 quantities $q^1_{CS}$ of the cash-subsidy game with government budget $b$: backward induction through the trader's Period-2 pricing, the government's welfare-maximizing subsidy and the trader's Period-1 release. Write $\bar b=(8+4g+g^2)/32$. Then $\mathrm{EqQ1}(b)\ne\emptyset$ for every $b\ge0$, and there is a threshold $t_1$ with $0<t_1<\bar b$ such that:
--
--   1. (i)(a), (ii)(a): for $0\le b<t_1$, $\mathrm{EqQ1}(b)=\{q^1_\phi\}$, and $q^1_\phi\in\mathrm{EqQ1}(t_1)$;
--   2. (i)(b): for $t_1<b\le\bar b$, every $q^1_{CS}\in\mathrm{EqQ1}(b)$ satisfies $q^1_{CS}\ge q^1_\phi$;
--   3. (i)(c): for $b>\bar b$, every $q^1_{CS}\in\mathrm{EqQ1}(b)$ satisfies $q^1_{CS}<q^1_\phi$;
--   4. (ii)(b): for $t_1<b<b'$, every $q\in\mathrm{EqQ1}(b)$ and $q'\in\mathrm{EqQ1}(b')$ satisfy
--   $$q'\le q .$$
--
--   In words: a small cash-subsidy budget leaves the artificial shortage unchanged, a moderate one mitigates it, and a large one aggravates it, with the Period-1 release non-increasing in the budget above $t_1$.
--
--   **Formalization Note** $t_1$ (Lemma O.1, not in the paper) is existential. It is pinned by the constancy below $t_1$ and the monotonicity above it, because $q^1_{CS}$ jumps up at $t_1$. At $b=t_1$ the two modes of the trader's objective tie, so only $q^1_\phi\in\mathrm{EqQ1}(t_1)$ is asserted. "Decreases" is read as non-increasing: for $g<1$ the quantity is constant at $(1-g)/2$ for $b\ge1+g(1+g)/2$, so the strict reading is false. The added assumption $g<4$ keeps $q^1_\phi>0$. The statement is about the equilibrium set itself, not about the closed forms of Theorem 2.
-- source:
--   Levi, Singhvi & Zheng, Artificial Shortage in Agricultural Supply Chains, SSRN 3332493 (version of 2021-04-14; MSOM forthcoming), p. 22, Proposition 3; notation p. 21

import Mathlib
import Definitions.Def_ArtShortage_CashSubsidy_Model

namespace ArtShortage.CashSubsidy

theorem proposition_3 (g lam : ℝ) (hS : Standing g lam) :
    (∀ b, 0 ≤ b → (EqQ1 g lam b).Nonempty) ∧
    ∃ t1 : ℝ, 0 < t1 ∧ t1 < (8 + 4 * g + g^2) / 32 ∧
      -- (i)(a) and (ii)(a)
      (∀ b, 0 ≤ b → b < t1 → EqQ1 g lam b = {1/2 - g/8}) ∧
      (1/2 - g/8) ∈ EqQ1 g lam t1 ∧
      -- (i)(b)
      (∀ b, t1 < b → b ≤ (8 + 4 * g + g^2) / 32 → ∀ q ∈ EqQ1 g lam b, 1/2 - g/8 ≤ q) ∧
      -- (i)(c)
      (∀ b, (8 + 4 * g + g^2) / 32 < b → ∀ q ∈ EqQ1 g lam b, q < 1/2 - g/8) ∧
      -- (ii)(b)
      (∀ b b', t1 < b → b < b' → ∀ q ∈ EqQ1 g lam b, ∀ q' ∈ EqQ1 g lam b', q' ≤ q) := by sorry

end ArtShortage.CashSubsidy
