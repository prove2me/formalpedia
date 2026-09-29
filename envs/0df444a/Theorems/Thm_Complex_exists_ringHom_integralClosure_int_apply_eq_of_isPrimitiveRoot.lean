-- Prove2me | Theorems.Thm_Complex_exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot
-- name    : Complex.exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/1655a4d8-487f-519c-addd-42340f7c6d72
-- title:
--   Reduction of ℤ̄ to K sending e^{2π i/M} to ζ
-- statement:
--   Let $\ell$ be a prime number and $M$ a nonzero natural number with $\ell \nmid M$. Let $K$ be an algebraically closed field of characteristic $\ell$, and let $\zeta \in K$ be a primitive $M$-th root of unity, in the sense that $\zeta^M = 1$ and $\zeta$ is not annihilated by any proper divisor condition, i.e. `IsPrimitiveRoot ζ M` holds. Write $\bar{\mathbb{Z}} =$ `integralClosure ℤ ℂ` for the ring of complex algebraic integers, realised as the subring of $\mathbb{C}$ of elements integral over $\mathbb{Z}$. The assertion is that there exists a ring homomorphism $\varphi : \bar{\mathbb{Z}} \to K$ such that every $z \in \bar{\mathbb{Z}}$ whose underlying complex number equals $\exp(2\pi i/M)$ satisfies $\varphi(z) = \zeta$. Since the inclusion $\bar{\mathbb{Z}} \hookrightarrow \mathbb{C}$ is injective, there is exactly one such $z$, so the conclusion is a normalised reduction map on the algebraic integers carrying the standard primitive $M$-th root of unity $\exp(2\pi i/M)$ to the prescribed $\zeta$. No further compatibility (for instance with a prescribed prime of $\bar{\mathbb{Z}}$ above $\ell$) is asserted.
--
--   This is the normalisation device for comparing characteristic-zero and characteristic-$\ell$ coefficients: a reduction map $\bar{\mathbb{Z}} \to K$ pinned down on $M$-th roots of unity. It is used to transport $q$-expansions and Hecke data from complex modular forms and modular curves to an algebraically closed field of characteristic $\ell$, being cited by the statements on Hecke operators at level structures and on $q$-expansions of function fields of the modular curves $X_H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Complex.exists_ringHom_integralClosure_int_apply_eq_of_isPrimitiveRoot
    (ℓ : ℕ) [Fact ℓ.Prime] (M : ℕ) [NeZero M] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (ζ : K) (hζ : IsPrimitiveRoot ζ M) :
    ∃ φ : integralClosure ℤ ℂ →+* K,
      ∀ z : integralClosure ℤ ℂ,
        (z : ℂ) = Complex.exp (2 * Real.pi * Complex.I / M) → φ z = ζ := by sorry
