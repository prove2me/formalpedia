-- Prove2me | Theorems.Thm_CourierDispatch_Exogenous_unique_root
-- name    : CourierDispatch.Exogenous.unique_root
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T23:12:19.725855+00:00
-- url     : https://prove2.me/theorems/3749ba48-4d43-4d75-97df-d4740818ab1f
-- title:
--   Proof of Propositions 1 and 2, Online Appendix p. 1 — f has a unique zero a₁ ≈ 0.5689 on (0, T₁), with f < 0 before it and f > 0 after it
-- statement:
--   Let $C_B\in[0.58,0.59]$ and let $f_A$ be the bracket of (A.1),
--   $$f_A(a)=\frac{a^2C_D}{2T_1(T_1-a)}-\frac12-\frac{a^2C_B}{T_2(T_2-a)}-\frac a3,\qquad T_1=\tfrac34,\ T_2=\tfrac{45\pi}{2(32+15\pi)},\ C_D=\tfrac98 .$$
--   Then there is $a_1$ with
--   $$0.56<a_1<0.58,\qquad f_A(a_1)=0,$$
--   such that $f_A(a)<0$ for $0<a<a_1$ and $f_A(a)>0$ for $a_1<a<T_1$. In particular $a_1$ is the unique zero of $f_A$ on $(0,T_1)$.
--
--   This is the single-crossing fact behind both threshold propositions: dedicated delivery has the shorter wait exactly when $\lambda r<a_1$.
--
--   **Formalization Note** The paper states $a_1\approx 0.5689$ for $C_2=0.583$; the bounds $0.56<a_1<0.58$ record that approximation and hold over the whole bracket. The paper's second positive root $a_2\approx 1.150$ lies beyond both stability bounds $T_1$ and $T_2$ and is not stated.
-- source:
--   Chen, Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063 (version of 2022-09-21), Online Appendix p. 1, proof of Propositions 1 and 2, after (A.2)

import Mathlib
import Definitions.Def_CourierDispatch_Exogenous_Setting

namespace CourierDispatch.Exogenous

/-- Proof of Propositions 1 and 2, Online Appendix p. 1: on `(0, T₁) = (0, 3/4)` the bracket of (A.1)
has exactly one zero `a₁ ≈ 0.5689`, negative before it and positive after it. -/
theorem unique_root (CB : ℝ) (hCB : CBRange CB) :
    ∃ a₁ : ℝ, 0 < a₁ ∧ a₁ < TD ∧ 56 / 100 < a₁ ∧ a₁ < 58 / 100 ∧ fA CB a₁ = 0 ∧
      (∀ a : ℝ, 0 < a → a < a₁ → fA CB a < 0) ∧
      (∀ a : ℝ, a₁ < a → a < TD → 0 < fA CB a) := by sorry

end CourierDispatch.Exogenous
