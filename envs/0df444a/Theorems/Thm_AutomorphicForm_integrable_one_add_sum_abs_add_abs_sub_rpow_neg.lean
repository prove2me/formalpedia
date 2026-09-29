-- Prove2me | Theorems.Thm_AutomorphicForm_integrable_one_add_sum_abs_add_abs_sub_rpow_neg
-- name    : AutomorphicForm.integrable_one_add_sum_abs_add_abs_sub_rpow_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/36c66a4a-5957-5084-a098-b67e8db1b493
-- title:
--   Integrability of (1+sumᵥ(|t+τᵥ|+|t-τ'ᵥ|))^{-B} for B≥ 2
-- statement:
--   Let $V$ be a non-empty finite type, let $\tau,\tau'\colon V\to\mathbb{R}$ be arbitrary real-valued functions on $V$, and let $B$ be a real number with $2\le B$. The assertion is that the function
--   $$t\longmapsto \Bigl(1+\sum_{v\in V}\bigl(|t+\tau(v)|+|t-\tau'(v)|\bigr)\Bigr)^{-B},$$
--   where the exponentiation is the real power function on the (strictly positive) base and the exponent is $-B$, is integrable on $\mathbb{R}$ with respect to the Lebesgue measure, in the sense of `MeasureTheory.Integrable`: it is almost everywhere strongly measurable and has finite integral of its absolute value. Note that the hypothesis $2\le B$ is stronger than what the comparison argument needs (any $B>1$ would do), and that non-emptiness of $V$ is essential, since for empty $V$ the function is the constant $1$, which is not integrable on $\mathbb{R}$.
--
--   This is an elementary integrability estimate for the archimedean weight profile attached to a finite set of real parameters $\tau_v,\tau'_v$. It serves as the integrability clause of [`AutomorphicForm.exists_forall_integrable_and_summable_rpow_neg_archParam_of_isUnitaryChar_of_pairwise_ne`](thm.html#AutomorphicForm.exists_forall_integrable_and_summable_rpow_neg_archParam_of_isUnitaryChar_of_pairwise_ne), where $V$ plays the role of the set of archimedean places and the $\tau_v,\tau'_v$ of archimedean parameters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrable_one_add_sum_abs_add_abs_sub_rpow_neg.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.integrable_one_add_sum_abs_add_abs_sub_rpow_neg
    (V : Type) [Fintype V] [Nonempty V] (τ τ' : V → ℝ) (B : ℝ) (hB : 2 ≤ B) :
    MeasureTheory.Integrable
      (fun t : ℝ => (1 + ∑ v : V, (|t + τ v| + |t - τ' v|)) ^ (-B)) := by sorry
