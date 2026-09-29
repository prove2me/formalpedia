-- Prove2me | Theorems.Thm_DiazModulus_recip_pi_log_of_pi_im_algebraic
-- name    : DiazModulus.recip_pi_log_of_pi_im_algebraic
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T14:19:10.098011+00:00
-- url     : https://prove2.me/theorems/ae6003d4-38d2-43ab-8555-0d54bcae017c
-- title:
--   An algebraic $\pi\,\operatorname{Im} u$ forces an algebraic multiple of $1/(i\pi)$ into $\mathcal{L}$
-- statement:
--   Let $u \in \mathbb{C}$ with $e^{u}$ algebraic, and suppose $\operatorname{Im} u$ is **not** a rational multiple of $\pi$ but $\pi \cdot \operatorname{Im} u$ **is** algebraic. Then there is an algebraic $\gamma \neq 0$ with $e^{\gamma/(i\pi)}$ algebraic.
--
--   This is the exact analogue, for the degenerate case $r = 0$, of the published `DiazModulus.recip_pi_log_of_period_aligned`, which carries the same conclusion under the period-aligned hypothesis $\exists r \in \mathbb{Q}^{\times}$ with $\pi(\operatorname{Im} u + r\pi) \in \overline{\mathbb{Q}}$.
--
--   The proof is shorter than the aligned one, because no period translate is involved: with $\nu = (u - \bar u)/2 = i \operatorname{Im} u$ one has $e^{2\nu} = e^{u}/\overline{e^{u}}$, so $e^{\nu}$ is algebraic, and $-\pi \operatorname{Im} u$ is the required $\gamma$ since $\gamma/(i\pi) = \nu$.
--
--   Together with `DiazModulus.recip_pi_not_log` this closes the leaf `DiazModulus.diaz_of_exp_not_real_irrational_angle_period_free_pi_im_algebraic`.
-- source:
--   The r = 0 route lemma for the period-free / pi-Im-algebraic leaf; analogue of DiazModulus.recip_pi_log_of_period_aligned.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem recip_pi_log_of_pi_im_algebraic :
    ∀ u : ℂ, (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
      IsAlgebraic ℚ ((Real.pi * u.im : ℝ) : ℂ) →
      IsAlgebraic ℚ (Complex.exp u) →
      ∃ γ : ℂ, IsAlgebraic ℚ γ ∧ γ ≠ 0 ∧
        IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by sorry
end DiazModulus
