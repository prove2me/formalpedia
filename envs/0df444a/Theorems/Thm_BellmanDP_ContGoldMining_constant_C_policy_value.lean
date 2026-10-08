-- Prove2me | Theorems.Thm_BellmanDP_ContGoldMining_constant_C_policy_value
-- name    : BellmanDP.ContGoldMining.constant_C_policy_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T17:15:47.407075+00:00
-- url     : https://prove2.me/theorems/75cd45ef-3e34-4246-8a93-f798aededa89
-- title:
--   Chapter VIII, § 15, Eq. (1) (corrected) — $f_C(\infty) = r_3x_0/(q_3+r_3) + r_4y_0/(q_3+r_4)$
-- statement:
--   Consider the three-choice continuous gold-mining process with positive rates $q_1, q_2, q_3, r_1, r_2, r_3, r_4$ and initial amounts $x_0, y_0 \ge 0$. If decision $C$ is used for all $t \ge 0$ ($\varphi_3 \equiv 1$), then $x(t) = x_0 e^{-r_3 t}$, $y(t) = y_0 e^{-r_4 t}$, $p(t) = e^{-q_3 t}$, and the expected total gold is
--   $$f_C(\infty) = \frac{r_3 x_0}{q_3 + r_3} + \frac{r_4 y_0}{q_3 + r_4}.$$
--
--   Bellman compares this value with $f_B(\infty) = r_2 y_0/(q_2 + r_2)$ to show that near the $y$-axis $B$ is preferable to $C$.
--
--   **Formalization Note** The book prints the first denominator as $q_2 + r_3$. That is a misprint: under $C$ the machine fails at rate $q_3$, and the value above is the integral $\int_0^\infty e^{-q_3 t}(r_3 x_0 e^{-r_3 t} + r_4 y_0 e^{-r_4 t})\,dt$. For $x_0 = 1$, $y_0 = 0$, $q_2 = 1$, $q_3 = 2$, $r_3 = 1$ the process yields $1/3$, while the printed formula gives $1/2$. $f(\infty)$ is an extended nonnegative real, so the identity is stated with `ENNReal.ofReal`.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter VIII, § 15, proof of Lemma 6, Eq. (1), p. 237

import Mathlib
import Definitions.Def_BellmanDP_ContGoldMining_Process

namespace BellmanDP.ContGoldMining

/-- Bellman, *Dynamic Programming*, Ch. VIII, § 15, proof of Lemma 6, Eq. (1), p. 237, corrected:
using `C` for all `t ≥ 0` yields `f_C(∞) = r₃ x₀/(q₃ + r₃) + r₄ y₀/(q₃ + r₄)`
(the print has `q₂ + r₃` in the first denominator). -/
theorem constant_C_policy_value (P : Params) (hP : P.Positive) (x₀ y₀ : ℝ) (hx₀ : 0 ≤ x₀)
    (hy₀ : 0 ≤ y₀) :
    goldInfty P x₀ y₀ (fun i _ => ![0, 0, 1] i) =
      ENNReal.ofReal (P.r₃ * x₀ / (P.q₃ + P.r₃) + P.r₄ * y₀ / (P.q₃ + P.r₄)) := by sorry

end BellmanDP.ContGoldMining
