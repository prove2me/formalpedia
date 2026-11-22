-- Prove2me | Theorems.Thm_ExplicitFormula_poisson_summation_mellin_of_piecewise_smooth
-- name    : ExplicitFormula.poisson_summation_mellin_of_piecewise_smooth
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:31:40.373797+00:00
-- url     : https://prove2.me/theorems/b77be89c-0284-4860-bc4e-e083b7b7640d
-- title:
--   Proposition B.4.1.2 (corrected) — Poisson summation along $\theta^{\mathbb Z}$ with jump singularities: midpoint values against symmetric sums of Mellin samples
-- statement:
--   **Poisson summation along a geometric progression for functions with jump singularities** (Proposition B.4.1.2, in corrected form).
--
--   Let $\phi\colon\mathbb R_{>0}\to\mathbb C$ and $g(x)=\phi(e^x)$ satisfy the hypotheses of Lemma B.4.1.1:
--
--   1. there is a finite set $S\subset\mathbb R$ such that $g$ is $C^\infty$ on $\mathbb R\setminus S$ and, for every $k\ge0$ and $x\in S$, both one-sided limits $\lim_{u\to x^\pm}g^{(k)}(u)$ exist;
--   2. for every integer $N\ge0$ there are $C_N,T_N>0$ with $|g(x)|<C_Ne^{-N|x|}$ and $|g'(x)|<C_Ne^{-N|x|}$ for $|x|>T_N$.
--
--   Let $\Phi(s)=\int_0^\infty\phi(t)\,t^s\,\frac{dt}{t}$ be the Mellin transform of $\phi$ (an entire function). Let $\theta>0$, $\theta\neq1$, and let $\chi$ be a unitary character of the discrete group $\theta^{\mathbb Z}\subset\mathbb R_{>0}$; it is determined by $c=\chi(\theta)\in U(1)$, namely $\chi(\theta^m)=c^m$. Let $\ell\in\mathbb C$ be any logarithm of $\chi(\theta)$, i.e. $e^{\ell}=c$. For $t>0$ write $\phi(t^\pm)=\lim_{u\to t^\pm}\phi(u)$. Then:
--
--   1. the series $\sum_{m\in\mathbb Z}\chi(\theta^m)\,\tfrac12\big(\phi((\theta^m)^+)+\phi((\theta^m)^-)\big)$ converges absolutely;
--   2. the symmetric partial sums of the Mellin samples converge, and
--   $$\lim_{N\to\infty}\ \sum_{|m|\le N}\Phi\!\left(\frac{\ell+2\pi i m}{\log\theta}\right)=|\log\theta|\sum_{m\in\mathbb Z}\chi(\theta^m)\,\frac{\phi((\theta^m)^+)+\phi((\theta^m)^-)}{2}.$$
--
--   In particular the left-hand side does not depend on the choice of the logarithm $\ell$. For all but finitely many $m$ the midpoint value is simply $\phi(\theta^m)$ (Remark B.4.1.3). The series on the left is in general not absolutely convergent (Remark B.4.1.4): for $\phi=1_{[1,2]}$, $\theta=2$, $\chi=1$ one has $\Phi(s)=(2^s-1)/s$, all samples with $m\ne0$ vanish, and both sides equal $\log 2$.
--
--   This is the Poisson summation formula for the lattice $(\log\theta)\mathbb Z\subset\mathbb R$, applied to the piecewise smooth function $x\mapsto e^{\ell x/\log\theta}g(x)$ and combined with Dirichlet's theorem on the pointwise convergence of Fourier series at jump points. The source uses it to express the local Dirac combs $\sum_m\chi(\mathfrak p^m)\phi(N(\mathfrak p)^m)$ of the explicit formulas through the Mellin transform (Lemma B.4.1.7).
--
--   **Deviation from the source.** Equation (B.4.1.7) is printed with the factor $\log\theta$ instead of $|\log\theta|$; this is wrong for $0<\theta<1$ (for $\theta=1/2$, $\chi=1$, $\phi=1_{[1,2]}$ the printed sides are $-\log2$ and $\log 2$). The symbol $\log\chi(\theta)$ of the source has to be read as an ordinary logarithm $\ell$ of the complex number $\chi(\theta)$ (p. 607 introduces it as $ix$ with $\chi(\theta^m)=\theta^{imx}$, which is off by the factor $\log\theta$), and the "convergent" series on the right of (B.4.1.7) is the limit of the symmetric partial sums. These corrections are the ones recorded in the errata of the upstream formalization (item I94).
--
--   **Formalization Note.** As in Lemma B.4.1.1, $\phi$ is represented by its logarithmic profile `g`, so that the points $\theta^m$ become the lattice points $m\log\theta$ and $\Phi$ is `mellin (fun t => g (Real.log t))`. The value $\chi(\theta)$ is an element `c : Circle` and `ℓ` satisfies `Complex.exp ℓ = c`. The one-sided limits are `limUnder (𝓝[<] x) g` and `limUnder (𝓝[>] x) g`; they exist at every point (by continuity off `S`, by hypothesis on `S`), and their average does not depend on which of the two is the limit from the left, so the change of orientation for $\theta<1$ is harmless. The first conjunct (`Summable`) guarantees that the `tsum` in the limit is a genuine sum.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 608, Proposition B.4.1.2, eq. (B.4.1.7), in the corrected form recorded in the statement (proof on pp. 609-610); classical references given by the paper: M. A. Pinsky, Introduction to Fourier Analysis and Wavelets, Graduate Studies in Mathematics 102, AMS, 2002, Ch. 4, §4.2, Exercise 4.2.9, p. 226 (case of the trivial character), and L. Hörmander, The Analysis of Linear Partial Differential Operators I, Springer, 1983, Ch. VII, Theorem 7.2.1 (Remark B.4.1.5, p. 610)

import Mathlib

open Filter Topology
open scoped Real ContDiff

set_option autoImplicit false

namespace ExplicitFormula

theorem poisson_summation_mellin_of_piecewise_smooth
    (g : ℝ → ℂ) (S : Finset ℝ)
    (hsmooth : ContDiffOn ℝ ∞ g (S : Set ℝ)ᶜ)
    (hlim : ∀ (j : ℕ) (x : ℝ), x ∈ S →
      (∃ l : ℂ, Tendsto (iteratedDeriv j g) (𝓝[<] x) (𝓝 l)) ∧
      (∃ r : ℂ, Tendsto (iteratedDeriv j g) (𝓝[>] x) (𝓝 r)))
    (hdecay : ∀ N : ℕ, ∃ C > (0 : ℝ), ∃ T > (0 : ℝ), ∀ x : ℝ, T < |x| →
      ‖g x‖ < C * Real.exp (-(N : ℝ) * |x|) ∧ ‖deriv g x‖ < C * Real.exp (-(N : ℝ) * |x|))
    (θ : ℝ) (hθ : 0 < θ) (hθ₁ : θ ≠ 1) (c : Circle) (ℓ : ℂ) (hℓ : Complex.exp ℓ = (c : ℂ)) :
    Summable (fun m : ℤ => (c : ℂ) ^ m *
      ((limUnder (𝓝[<] ((m : ℝ) * Real.log θ)) g +
        limUnder (𝓝[>] ((m : ℝ) * Real.log θ)) g) / 2)) ∧
    Tendsto
      (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        mellin (fun t : ℝ => g (Real.log t)) ((ℓ + 2 * π * Complex.I * m) / Real.log θ))
      atTop
      (𝓝 ((|Real.log θ| : ℝ) * ∑' m : ℤ, (c : ℂ) ^ m *
        ((limUnder (𝓝[<] ((m : ℝ) * Real.log θ)) g +
          limUnder (𝓝[>] ((m : ℝ) * Real.log θ)) g) / 2))) := by sorry

end ExplicitFormula
