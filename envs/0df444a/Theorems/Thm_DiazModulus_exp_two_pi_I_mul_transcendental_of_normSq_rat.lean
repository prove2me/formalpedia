-- Prove2me | Theorems.Thm_DiazModulus_exp_two_pi_I_mul_transcendental_of_normSq_rat
-- name    : DiazModulus.exp_two_pi_I_mul_transcendental_of_normSq_rat
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T18:03:18.89138+00:00
-- url     : https://prove2.me/theorems/9a4ca87e-2ccf-4e2f-a5c7-a7554b576a21
-- title:
--   e^{2πiτ} is transcendental when τ is non-real, algebraic over ℚ(π), and |τ|² is rational
-- statement:
--   Let $\tau \in \mathbb C \setminus \mathbb R$ be algebraic over $\mathbb Q(\pi)$, with $|\tau|^2 \in \mathbb Q$. Then $e^{2\pi i \tau}$ is transcendental.
--
--   Diaz (1997, property (4-1)) states the transcendence of $e^{2\pi i\tau}$ for every $\tau$ in the upper half-plane with $|\tau|^2 \in \mathbb Q$, as a consequence of conjectures; in particular, conjecturally, the only algebraic point of the curve $z \mapsto e^{2\pi i z}$ on the unit circle is $1$. This node proves the case in which $\tau$ is algebraic over $\mathbb Q(\pi)$. It follows from his Proposition 1 (`DiazModulus.log_pair_algebraicIndependent_of_mul_eq_rat_pi_sq`) applied to $\ell_1 = 2\pi i\tau$ and its complex conjugate $\ell_2 = \overline{\ell_1}$, whose product is $4|\tau|^2\pi^2$: the proposition makes $\ell_1$ and $2\pi i$ algebraically independent, while both are algebraic over $\mathbb Q(\pi)$.
-- source:
--   Background: G. Diaz, La conjecture des quatre exponentielles et les conjectures de D. Bertrand sur la fonction modulaire, J. Théor. Nombres Bordeaux 9 (1997), 229–245, property (4-1) (conjectural in general) and Proposition 1, from which this case follows. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi).

import Mathlib

open ComplexConjugate

namespace DiazModulus

theorem exp_two_pi_I_mul_transcendental_of_normSq_rat (τ : ℂ) (hτ : τ.im ≠ 0)
    (halg : IsAlgebraic ↥(Algebra.adjoin ℚ ({((Real.pi : ℝ) : ℂ)} : Set ℂ)) τ)
    (c : ℚ) (hc : τ * conj τ = (c : ℂ)) :
    Transcendental ℚ (Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * τ)) := by
  sorry

end DiazModulus
