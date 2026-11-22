-- Prove2me | Theorems.Thm_EntireDivisor_exists_eq_mul_iff_iteratedDeriv_eq_zero
-- name    : EntireDivisor.exists_eq_mul_iff_iteratedDeriv_eq_zero
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:34:59.661602+00:00
-- url     : https://prove2.me/theorems/d26ca413-730c-4748-b871-3b8b7a865bee
-- title:
--   Divisor sequence on $\mathbb C$, middle exactness: an entire $g$ is a multiple of $f$ iff its jets of order $<\operatorname{ord}_z f$ vanish
-- statement:
--   **Divisor exact sequence of entire functions, exactness in the middle.** Let $f:\mathbb C\to\mathbb C$ be an entire function and, for $z\in\mathbb C$, let $N(z)=\operatorname{ord}_z f\in\mathbb N\cup\{\infty\}$ be its order of vanishing at $z$ (so $N(z)=0$ when $f(z)\neq0$, and $N\equiv\infty$ when $f\equiv0$). Then for every entire function $g:\mathbb C\to\mathbb C$ the following are equivalent:
--
--   1. $g=f\,h$ for some entire function $h$;
--   2. $g^{(m)}(z)=0$ for every $z\in\mathbb C$ and every integer $m$ with $0\le m<N(z)$.
--
--   Equivalently, writing $D=\operatorname{div}(f)$ for $f\not\equiv0$, the kernel of the jet map
--   $$J_f:\ \mathcal O(\mathbb C)\longrightarrow\prod_{z:\,f(z)=0}\mathbb C^{N(z)},\qquad g\longmapsto\bigl(g^{(m)}(z)\bigr)_{z,\;0\le m<N(z)},$$
--   is exactly the ideal $f\cdot\mathcal O(\mathbb C)$, i.e. the global sections of $\mathscr O_X(-D)$ on $X=\mathbb C$. Together with the injectivity of $h\mapsto fh$ (identity theorem) and the surjectivity of $J_f$ (Weierstrass interpolation, `EntireDivisor.exists_differentiable_iteratedDeriv_eq`), this is the exactness of the sequence of global sections
--   $$0\to H^0(\mathbb C,\mathscr O_X(-D))\to H^0(\mathbb C,\mathscr O_X)\to H^0(\mathbb C,\mathscr O_D)\to0 .$$
--
--   **Role in the source.** In §1.2.1 (p. 13, repeated in §1.8.3.1, p. 45) the paper calls the Mellin-transformed sequence $0\to L(s+1/2,\chi)((s+1/2)(s-1/2))^\delta\mathcal O(\mathbb C)\cap A\mathcal S(\mathbb C)\to A\mathcal S(\mathbb C)\to\prod_{z}\mathbb C^{N(z)}\to0$ its *fundamental divisor exact sequence*, because it mirrors the global sections of $0\to\mathscr O_X(-D)\to\mathscr O_X\to\mathscr O_D\to0$ for the Stein space $X=\mathbb C$ and $D=\operatorname{div}(L(s+1/2,\chi)((s+1/2)(s-1/2))^\delta)$. The present statement is the middle exactness of that classical model, for the divisor of an arbitrary entire function.
--
--   **Formalization Note.** "Entire" is `Differentiable ℂ`, the order of vanishing is Mathlib's `analyticOrderAt f z : ℕ∞`, and jets are `iteratedDeriv m g z`. The classical setting assumes $f\not\equiv0$ (so that $\operatorname{div}(f)$ is defined); this hypothesis is not imposed because the equivalence also holds for $f\equiv0$ (both sides then say $g\equiv0$).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 13, §1.2.1 (Fundamental Divisor Exact Sequence: global sections of $0\to\mathscr O_X(-D)\to\mathscr O_X\to\mathscr O_D\to0$ for the Stein space $X=\mathbb C$), repeated in §1.8.3.1, p. 45

import Mathlib

set_option autoImplicit false

namespace EntireDivisor

/-- Exactness in the middle of the divisor sequence `0 → 𝒪(-D) → 𝒪 → 𝒪_D → 0` on `ℂ`, `D = div f`:
an entire `g` is a multiple `f * h` of `f` by an entire `h` iff all jets of `g` of order
`< ord_z f` vanish at every `z`. -/
theorem exists_eq_mul_iff_iteratedDeriv_eq_zero (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    (∃ h : ℂ → ℂ, Differentiable ℂ h ∧ g = f * h) ↔
      ∀ z : ℂ, ∀ m : ℕ, (m : ℕ∞) < analyticOrderAt f z → iteratedDeriv m g z = 0 := by sorry

end EntireDivisor
