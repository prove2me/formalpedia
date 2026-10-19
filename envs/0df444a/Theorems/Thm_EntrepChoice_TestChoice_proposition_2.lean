-- Prove2me | Theorems.Thm_EntrepChoice_TestChoice_proposition_2
-- name    : EntrepChoice.TestChoice.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:11:23.739385+00:00
-- url     : https://prove2.me/theorems/22d41738-6c2e-4c31-a7fe-0d7cccc6182f
-- title:
--   Proposition 2, p. 17 — the strategy-biased test (λ_v, 1) has higher value than the idea-biased test (1, λ_s) if (1 − p₀)e₀(1 − λ_s)C > (1 − λ_v)p₀(1 − e₀)(e₀v − C)
-- statement:
--   Assume the standing assumptions $0<p_0<1$, $0<e_0<1$, $v>0$, $V_0 = e_0p_0v - C = 0$ and $c<C$. Let $\lambda_v,\lambda_s\in[0,1]$ be baseline precisions, and consider the **strategy-biased test** $(\lambda_v, 1)$ and the **idea-biased test** $(1, \lambda_s)$, each satisfying (A1). If
--   $$(1-p_0)e_0(1-\lambda_s)C > (1-\lambda_v)p_0(1-e_0)(e_0v - C),$$
--   then the strategy-biased test is strictly preferred:
--   $$V_0(1,\lambda_s) < V_0(\lambda_v, 1),$$
--   where $V_0(\cdot,\cdot)$ is the value of testing with optimal period-1 actions.
--
--   The benefit of a high $\lambda_s$ is more efficient abandonment of a poor idea; the benefit of a high $\lambda_v$ is more efficient continuation with an alternative strategy. The condition weighs the two, so the test preference is biased by the prior $(p_0,e_0)$.
--
--   **Formalization Note.** "Preferred" is read as strictly larger value of testing (the entrepreneur and mentor share the objective in §5.1). (A1) is assumed for the two tests compared; (A1) at the baseline test $(\lambda_v,\lambda_s)$ implies both, so this is the weaker hypothesis. The paper's p. 7 requirement that all four posteriors be below $1$ is relaxed for the precise tests, as §5.1 itself does. The value $V_0(\lambda_v,\lambda_s)$ of p. 10 is `testValue`, the optimum over the three period-1 actions built from the signal table, not a closed form.
-- source:
--   Agrawal, Gans & Stern, Enabling Entrepreneurial Choice, NBER Working Paper 27379 (June 2020), Proposition 2, p. 17; tests named in §5.2, p. 19

import Mathlib
import Definitions.Def_EntrepChoice_TestChoice_Setting

namespace EntrepChoice.TestChoice
theorem proposition_2 (P : Params) (hP : Standing P) (lv ls : ℝ)
    (hlv : 0 ≤ lv ∧ lv ≤ 1) (hls : 0 ≤ ls ∧ ls ≤ 1)
    (hA_strat : A1 P ⟨lv, 1⟩) (hA_idea : A1 P ⟨1, ls⟩)
    (hcond : (1 - lv) * P.p0 * (1 - P.e0) * (P.e0 * P.v - P.C)
               < (1 - P.p0) * P.e0 * (1 - ls) * P.C) :
    testValue P ⟨1, ls⟩ < testValue P ⟨lv, 1⟩ := by sorry
end EntrepChoice.TestChoice
