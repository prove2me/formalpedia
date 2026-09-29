-- Prove2me | Theorems.Thm_DiazModulus_recip_pi_log_of_period_aligned
-- name    : DiazModulus.recip_pi_log_of_period_aligned
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T10:38:40.585235+00:00
-- url     : https://prove2.me/theorems/3c3c214a-3979-4ce1-80ee-207b2a7afc02
-- title:
--   A period-aligned candidate makes an algebraic multiple of 1/(iπ) a logarithm
-- statement:
--   **A period-aligned counterexample to Diaz's modulus conjecture would make an algebraic
--   multiple of $1/(i\pi)$ a logarithm of an algebraic number.**
--
--   **Statement.** Let $u\in\mathbb C$ with $\Im u\notin\pi\mathbb Q$ and $e^{u}\in\overline{\mathbb Q}$,
--   and suppose $\pi(\Im u+r\pi)\in\overline{\mathbb Q}$ for some $r\in\mathbb Q^{\times}$. Then there is
--   $\gamma\in\overline{\mathbb Q}^{\times}$ with $e^{\gamma/(i\pi)}\in\overline{\mathbb Q}$, that is,
--   $\gamma/(i\pi)\in\mathcal L$.
--
--   **This is not a decomposition.** It is a route lemma: there is no reduction edge to submit for it,
--   and it neither follows from nor implies the mission's target. It is published because it is what
--   makes `DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned` attackable. That child
--   follows at once from
--   $$\gamma/(i\pi)\notin\mathcal L\quad\text{for every }\gamma\in\overline{\mathbb Q}^{\times},$$
--   equivalently "$1/\pi$ is not, up to an algebraic factor, a logarithm of an algebraic number" — a
--   statement about $\pi$ alone, implied by the strong four exponentials conjecture (take
--   $x=(1,\nu)$, $y=(1,i\pi)$), open, and far more special than the leaf.
--
--   **Proof.** Put $\nu=i(\Im u+r\pi)$. It is non-zero because $\Im u\notin\pi\mathbb Q$. Then
--   $(i\pi)\,\nu=-\pi(\Im u+r\pi)\in\overline{\mathbb Q}^{\times}$, which is $\gamma$ up to sign, and
--   $\nu=\gamma/(i\pi)$. It remains to see $\nu\in\mathcal L$: with $d=\operatorname{den} r$ and
--   $c=\operatorname{num} r$ one has $2d\,\nu=d\,(u-\bar u)+c\,(2\pi i)$, hence
--   $$\bigl(e^{\nu}\bigr)^{2d}=\bigl(e^{u}/\overline{e^{u}}\bigr)^{d}\cdot e^{c\cdot 2\pi i}
--   =\bigl(e^{u}/\overline{e^{u}}\bigr)^{d},$$
--   which is algebraic; and a complex number whose $2d$-th power is algebraic is algebraic.
--
--   **What is not used.** No transcendence input at all: not Hermite–Lindemann, not the transcendence
--   of $\pi$, not six exponentials. Nor is $|u|$ algebraic, nor $u\neq0$, nor $e^{u}\notin\mathbb R$
--   used — the leaf's remaining clauses are irrelevant to this implication, which is why the statement
--   carries only three hypotheses.
--
--   **Novelty.** Elementary; it is Proposition 3.8 of Carlo Perassi's companion note to
--   https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9). No claim of novelty is made.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Proposition 3.8. Formal proof: Diaz modulus mission, 8 September 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem recip_pi_log_of_period_aligned :
    ∀ u : ℂ, (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
      (∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
      IsAlgebraic ℚ (Complex.exp u) →
      ∃ γ : ℂ, IsAlgebraic ℚ γ ∧ γ ≠ 0 ∧
        IsAlgebraic ℚ (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by sorry
end DiazModulus
