-- Prove2me | Theorems.Thm_BoundedParamMDP_Optimal_lemma2_mdp_composition
-- name    : BoundedParamMDP.Optimal.lemma2_mdp_composition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:38.425997+00:00
-- url     : https://prove2.me/theorems/b2d300c0-b519-4a07-b000-211817c861d9
-- title:
--   Lemma 2 — $M_1\oplus^\pi_{\max}M_2$ dominates both, $M_1\oplus^\pi_{\min}M_2$ is dominated by both
-- statement:
--   Let $M_\updownarrow$ be a bounded-parameter MDP, $\pi$ a policy and $M_1,M_2\in M_\updownarrow$. The compositions $M_1\oplus^\pi_{\max}M_2$ and $M_1\oplus^\pi_{\min}M_2$ of Definition 5 are MDPs in $M_\updownarrow$, and
--
--   1. for $M_3=M_1\oplus^\pi_{\max}M_2$,
--   $$
--   V_{M_3,\pi}\ge_{\mathrm{dom}}V_{M_1,\pi}\quad\text{and}\quad V_{M_3,\pi}\ge_{\mathrm{dom}}V_{M_2,\pi};
--   $$
--   2. for $M_3=M_1\oplus^\pi_{\min}M_2$,
--   $$
--   V_{M_3,\pi}\le_{\mathrm{dom}}V_{M_1,\pi}\quad\text{and}\quad V_{M_3,\pi}\le_{\mathrm{dom}}V_{M_2,\pi}.
--   $$
--
--   Composing statewise the better (or worse) of two member MDPs is the step from which the existence of $\pi$-maximizing and $\pi$-minimizing MDPs (Theorem 7) is built.
--
--   **Formalization Note** A composition is given by its transition function; "$M_3=M_1\oplus^\pi_{\max}M_2$" means $M_3$ is a member whose transition function is that composition. The statement also records that such a member exists (Definition 5 presents the compositions as MDPs of $M_\updownarrow$).
-- source:
--   Givan, Leach, Dean, Bounded-parameter Markov decision processes, Artificial Intelligence (2000), manuscript of May 22, 2000, pp. 14–15, Lemma 2, eqs. (14)–(15) (restated p. 35)

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP
import Definitions.Def_BoundedParamMDP_Optimal_BMDP

namespace BoundedParamMDP.Optimal

/-- Lemma 2 (pp. 14–15): for a policy `π` and `M₁, M₂ ∈ M↕`, the compositions
`M₁ ⊕^π_max M₂` and `M₁ ⊕^π_min M₂` are MDPs in `M↕`, and
(a) for `M₃ = M₁ ⊕^π_max M₂`, `V_{M₃,π} ≥_dom V_{M₁,π}` and `V_{M₃,π} ≥_dom V_{M₂,π}`;
(b) for `M₃ = M₁ ⊕^π_min M₂`, `V_{M₃,π} ≤_dom V_{M₁,π}` and `V_{M₃,π} ≤_dom V_{M₂,π}`. -/
theorem lemma2_mdp_composition {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    (B : BMDP Q A) (π : Policy Q A) (M₁ M₂ : Member B) :
    ((∃ M₃ : Member B, M₃.1.F = composeMaxF π M₁.1 M₂.1) ∧
      ∀ M₃ : Member B, M₃.1.F = composeMaxF π M₁.1 M₂.1 →
        value M₁.1 π ≤ value M₃.1 π ∧ value M₂.1 π ≤ value M₃.1 π) ∧
    ((∃ M₃ : Member B, M₃.1.F = composeMinF π M₁.1 M₂.1) ∧
      ∀ M₃ : Member B, M₃.1.F = composeMinF π M₁.1 M₂.1 →
        value M₃.1 π ≤ value M₁.1 π ∧ value M₃.1 π ≤ value M₂.1 π) := by sorry

end BoundedParamMDP.Optimal
