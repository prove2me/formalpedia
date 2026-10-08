-- Prove2me | Theorems.Thm_BoundedParamMDP_Optimal_lemma1_order_maximizing_bracket
-- name    : BoundedParamMDP.Optimal.lemma1_order_maximizing_bracket
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:16.833898+00:00
-- url     : https://prove2.me/theorems/2435f13f-daa1-42b8-8adc-78c28b58d4b4
-- title:
--   Lemma 1 — values in $M_\updownarrow$ are bracketed by values in $X_{M_\updownarrow}$
-- statement:
--   Let $M_\updownarrow$ be a bounded-parameter MDP, $\pi$ a policy, $M\in M_\updownarrow$ a member MDP and $v:Q\to\mathbb R$ a value function. Then
--
--   1. there are order-maximizing MDPs $M_1,M_2\in X_{M_\updownarrow}$ with
--   $$
--   V_{M_1,\pi}\le_{\mathrm{dom}}V_{M,\pi}\le_{\mathrm{dom}}V_{M_2,\pi};
--   $$
--   2. there are order-maximizing MDPs $M_3,M_4\in X_{M_\updownarrow}$ with
--   $$
--   VI_{M_3,\pi}(v)\le_{\mathrm{dom}}VI_{M,\pi}(v)\le_{\mathrm{dom}}VI_{M_4,\pi}(v).
--   $$
--
--   Thus the finitely many order-maximizing MDPs already contain the extreme behaviours of the uncountable family $M_\updownarrow$, both for whole value functions and for a single backup.
--
--   **Formalization Note** "$M_i\in X_{M_\updownarrow}$" is stated as: $M_i$ is a member of $M_\updownarrow$ whose transition function is that of an order-maximizing MDP $M_O$ for some ordering $O$ (Definition 1 selects $M_O\in M_\updownarrow$; that it is a member is part of the claim).
-- source:
--   Givan, Leach, Dean, Bounded-parameter Markov decision processes, Artificial Intelligence (2000), manuscript of May 22, 2000, p. 11, Lemma 1 (restated p. 34, eqs. (34)–(35))

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP
import Definitions.Def_BoundedParamMDP_Optimal_BMDP

namespace BoundedParamMDP.Optimal

/-- Lemma 1 (p. 11, restated p. 34): for any policy `π`, any `M ∈ M↕` and any
`v : Q → ℝ`, (a) there are `M₁, M₂ ∈ X_{M↕}` with `V_{M₁,π} ≤_dom V_{M,π} ≤_dom V_{M₂,π}`;
(b) there are `M₃, M₄ ∈ X_{M↕}` with `VI_{M₃,π}(v) ≤_dom VI_{M,π}(v) ≤_dom VI_{M₄,π}(v)`.
An MDP lies in `X_{M↕}` when it is a member of `M↕` whose transition function is that of an
order-maximizing MDP `M_O`. -/
theorem lemma1_order_maximizing_bracket {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] (B : BMDP Q A) (π : Policy Q A) (M : Member B) (v : Q → ℝ) :
    (∃ M₁ M₂ : Member B, M₁.1.F ∈ XM B ∧ M₂.1.F ∈ XM B ∧
      value M₁.1 π ≤ value M.1 π ∧ value M.1 π ≤ value M₂.1 π) ∧
    (∃ M₃ M₄ : Member B, M₃.1.F ∈ XM B ∧ M₄.1.F ∈ XM B ∧
      VIpol M₃.1 π v ≤ VIpol M.1 π v ∧ VIpol M.1 π v ≤ VIpol M₄.1 π v) := by sorry

end BoundedParamMDP.Optimal
