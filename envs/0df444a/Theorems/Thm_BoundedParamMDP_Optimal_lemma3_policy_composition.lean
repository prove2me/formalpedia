-- Prove2me | Theorems.Thm_BoundedParamMDP_Optimal_lemma3_policy_composition
-- name    : BoundedParamMDP.Optimal.lemma3_policy_composition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:30.874555+00:00
-- url     : https://prove2.me/theorems/b813b11a-b269-42c9-b6fb-c90c909b083a
-- title:
--   Lemma 3 — the policy compositions $\pi_1\oplus_{\mathrm{opt}}\pi_2$ and $\pi_1\oplus_{\mathrm{pes}}\pi_2$ improve both components
-- statement:
--   Let $M_\updownarrow$ be a bounded-parameter MDP, $\pi_1,\pi_2\in\Pi$, $\pi_3=\pi_1\oplus_{\mathrm{opt}}\pi_2$ and $\pi_4=\pi_1\oplus_{\mathrm{pes}}\pi_2$. Then
--
--   1. $V_\uparrow{}_{\pi_3}\ge_{\mathrm{dom}}V_\uparrow{}_{\pi_1}$ and $V_\uparrow{}_{\pi_3}\ge_{\mathrm{dom}}V_\uparrow{}_{\pi_2}$;
--   2. if $V_\uparrow{}_{\pi_1}=V_\uparrow{}_{\pi_2}$, then $V_\updownarrow{}_{\pi_3}\ge_{\mathrm{opt}}V_\updownarrow{}_{\pi_1}$ and $V_\updownarrow{}_{\pi_3}\ge_{\mathrm{opt}}V_\updownarrow{}_{\pi_2}$;
--   3. $V_\downarrow{}_{\pi_4}\ge_{\mathrm{dom}}V_\downarrow{}_{\pi_1}$ and $V_\downarrow{}_{\pi_4}\ge_{\mathrm{dom}}V_\downarrow{}_{\pi_2}$;
--   4. if $V_\downarrow{}_{\pi_1}=V_\downarrow{}_{\pi_2}$, then $V_\updownarrow{}_{\pi_4}\ge_{\mathrm{pes}}V_\updownarrow{}_{\pi_1}$ and $V_\updownarrow{}_{\pi_4}\ge_{\mathrm{pes}}V_\updownarrow{}_{\pi_2}$.
--
--   Because $\ge_{\mathrm{opt}}$ is lexicographic, the composition does not improve both components in general; the lemma is the two-stage substitute used to build optimal policies (Theorem 8).
--
--   **Formalization Note** The interval orders are applied statewise. Part (4) is stated with $\pi_4$, as in the Appendix restatement (p. 36); the statement on p. 17 prints $\pi_3$ in part (4), a misprint (the proof on p. 39 works with $\pi_4=\pi_1\oplus_{\mathrm{pes}}\pi_2$).
-- source:
--   Givan, Leach, Dean, Bounded-parameter Markov decision processes, Artificial Intelligence (2000), manuscript of May 22, 2000, p. 36, Lemma 3 (Appendix restatement of Lemma 3, p. 17)

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP
import Definitions.Def_BoundedParamMDP_Optimal_BMDP

namespace BoundedParamMDP.Optimal

/-- Lemma 3 (p. 17, restated p. 36): with `π₃ = π₁ ⊕_opt π₂` and `π₄ = π₁ ⊕_pes π₂`,
(a) `V↑π₃ ≥_dom V↑π₁` and `V↑π₃ ≥_dom V↑π₂`;
(b) if `V↑π₁ = V↑π₂` then `V↕π₃ ≥_opt V↕π₁` and `V↕π₃ ≥_opt V↕π₂`;
(c) `V↓π₄ ≥_dom V↓π₁` and `V↓π₄ ≥_dom V↓π₂`;
(d) if `V↓π₁ = V↓π₂` then `V↕π₄ ≥_pes V↕π₁` and `V↕π₄ ≥_pes V↕π₂`. -/
theorem lemma3_policy_composition {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]
    (B : BMDP Q A) (π₁ π₂ : Policy Q A) :
    (upperV B π₁ ≤ upperV B (composeOpt B π₁ π₂) ∧
      upperV B π₂ ≤ upperV B (composeOpt B π₁ π₂)) ∧
    (upperV B π₁ = upperV B π₂ → ∀ q : Q,
      optLE (intervalV B π₁ q) (intervalV B (composeOpt B π₁ π₂) q) ∧
      optLE (intervalV B π₂ q) (intervalV B (composeOpt B π₁ π₂) q)) ∧
    (lowerV B π₁ ≤ lowerV B (composePes B π₁ π₂) ∧
      lowerV B π₂ ≤ lowerV B (composePes B π₁ π₂)) ∧
    (lowerV B π₁ = lowerV B π₂ → ∀ q : Q,
      pesLE (intervalV B π₁ q) (intervalV B (composePes B π₁ π₂) q) ∧
      pesLE (intervalV B π₂ q) (intervalV B (composePes B π₁ π₂) q)) := by sorry

end BoundedParamMDP.Optimal
