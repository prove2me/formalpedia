-- Prove2me | Theorems.Thm_EntireDivisor_exists_differentiable_iteratedDeriv_eq
-- name    : EntireDivisor.exists_differentiable_iteratedDeriv_eq
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T18:35:00.243195+00:00
-- url     : https://prove2.me/theorems/c98a23e3-5bd6-4f43-8d26-3cf3f103669d
-- title:
--   Weierstrass interpolation on $\operatorname{div}(f)$: the jet map $\mathcal O(\mathbb C)\to\prod_{f(z)=0}\mathbb C^{\operatorname{ord}_z f}$ is surjective
-- statement:
--   **Weierstrass interpolation on the divisor of an entire function.** Let $f:\mathbb C\to\mathbb C$ be an entire function that is not identically zero, and for $z\in\mathbb C$ let $N(z)=\operatorname{ord}_z f\in\mathbb N$ be its order of vanishing at $z$; thus $N(z)\ge1$ exactly at the zeros of $f$, which form a closed discrete subset of $\mathbb C$. Then for every family of complex numbers $(c_{z,m})_{z\in\mathbb C,\ m\in\mathbb N}$ there is an entire function $g$ such that
--   $$g^{(m)}(z)=c_{z,m}\qquad\text{for every }z\in\mathbb C\text{ with }f(z)=0\text{ and every integer }0\le m<N(z).$$
--
--   Equivalently, the jet map
--   $$J_f:\ \mathcal O(\mathbb C)\longrightarrow\prod_{z:\,f(z)=0}\mathbb C^{N(z)},\qquad g\longmapsto\bigl(g^{(m)}(z)\bigr)_{z,\;0\le m<N(z)},$$
--   is surjective: for $D=\operatorname{div}(f)$ on $X=\mathbb C$ the map $H^0(\mathbb C,\mathscr O_X)\to H^0(\mathbb C,\mathscr O_D)$ is onto. This is the right-hand end of the exact sequence of global sections of $0\to\mathscr O_X(-D)\to\mathscr O_X\to\mathscr O_D\to0$; the middle exactness is `EntireDivisor.exists_eq_mul_iff_iteratedDeriv_eq_zero`. It is the classical Weierstrass (Mittag-Leffler) interpolation theorem for entire functions, specialised to the divisor of $f$.
--
--   **Role in the source.** In §1.2.1 (p. 13, repeated in §1.8.3.1, p. 45) the paper's *fundamental divisor exact sequence* $0\to L(s+1/2,\chi)((s+1/2)(s-1/2))^\delta\mathcal O(\mathbb C)\cap A\mathcal S(\mathbb C)\to A\mathcal S(\mathbb C)\to\prod_{z}\mathbb C^{N(z)}\to0$ is presented as mirroring the global sections of $0\to\mathscr O_X(-D)\to\mathscr O_X\to\mathscr O_D\to0$ for the Stein space $X=\mathbb C$ and $D=\operatorname{div}(L(s+1/2,\chi)((s+1/2)(s-1/2))^\delta)$; the statement above is the classical surjectivity in that model.
--
--   **Formalization Note.** "Entire" is `Differentiable ℂ`, the order of vanishing is Mathlib's `analyticOrderAt f z : ℕ∞`, and the prescribed data are an arbitrary function `c : ℂ → ℕ → ℂ`, of which only the values $c_{z,m}$ with $f(z)=0$, $m<N(z)$ matter. The hypothesis $f\not\equiv0$ (given as `∃ z, f z ≠ 0`) is the classical one and is necessary: for $f\equiv0$ every order is $\infty$ and the conclusion would prescribe all derivatives at all points.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 13, §1.2.1 (Fundamental Divisor Exact Sequence: global sections of $0\to\mathscr O_X(-D)\to\mathscr O_X\to\mathscr O_D\to0$ for the Stein space $X=\mathbb C$), repeated in §1.8.3.1, p. 45

import Mathlib

set_option autoImplicit false

namespace EntireDivisor

/-- Weierstrass interpolation on the divisor of a nonzero entire function `f`: arbitrary jets of
order `< ord_z f` can be prescribed at the zeros `z` of `f` by an entire function, i.e. the jet map
`𝒪(ℂ) → ∏_{f(z)=0} ℂ^{ord_z f}` is surjective. -/
theorem exists_differentiable_iteratedDeriv_eq (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hf0 : ∃ z : ℂ, f z ≠ 0) (c : ℂ → ℕ → ℂ) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ z : ℂ, ∀ m : ℕ, (m : ℕ∞) < analyticOrderAt f z → iteratedDeriv m g z = c z m := by sorry

end EntireDivisor
