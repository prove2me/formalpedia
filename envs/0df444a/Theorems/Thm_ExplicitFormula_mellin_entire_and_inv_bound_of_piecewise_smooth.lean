-- Prove2me | Theorems.Thm_ExplicitFormula_mellin_entire_and_inv_bound_of_piecewise_smooth
-- name    : ExplicitFormula.mellin_entire_and_inv_bound_of_piecewise_smooth
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:31:38.113799+00:00
-- url     : https://prove2.me/theorems/cf57aba5-5302-4d04-b314-6abbc0696b1c
-- title:
--   Lemma B.4.1.1 — the Mellin transform of a function with finitely many jump singularities is entire and $O(1/|s|)$ on vertical strips
-- statement:
--   **Mellin transform of a function with finitely many jump singularities** (Lemma B.4.1.1: slow decay in the presence of isolated jump singularities).
--
--   Let $\phi\colon\mathbb R_{>0}\to\mathbb C$ be a function and write $g(x)=\phi(e^x)$ for $x\in\mathbb R$, so that $(t\partial_t)^k\phi$ corresponds to the $k$-th derivative $g^{(k)}$. Assume:
--
--   1. *(smooth away from finitely many jumps)* there is a finite set $S\subset\mathbb R$ such that $g$ is $C^\infty$ on $\mathbb R\setminus S$ and, for every $k\ge 0$ and every $x\in S$, both one-sided limits $\lim_{u\to x^\pm}g^{(k)}(u)$ exist in $\mathbb C$;
--   2. *(rapid decay in $|\log t|$)* for every integer $N\ge 0$ there are $C_N>0$ and $T_N>0$ such that
--   $$|g(x)|<C_N\,e^{-N|x|}\quad\text{and}\quad|g'(x)|<C_N\,e^{-N|x|}\qquad\text{for all }x\text{ with }|x|>T_N .$$
--
--   Then the Mellin transform
--   $$\Phi(s)=\int_0^\infty\phi(t)\,t^{s}\,\frac{dt}{t}=\int_{\mathbb R}g(x)\,e^{sx}\,dx$$
--   has the following properties.
--
--   1. The integral converges absolutely for every $s\in\mathbb C$.
--   2. $\Phi$ is an entire function.
--   3. $\Phi$ decays like $1/|s|$ on every vertical strip of bounded width: for all real numbers $a,b$ there are $C>0$ and $R>0$ such that
--   $$|\Phi(s)|\le\frac{C}{|s|}\qquad\text{whenever }a\le\operatorname{Re}(s)\le b\ \text{ and }\ |s|>R .$$
--
--   The rate $1/|s|$ cannot be improved in the presence of a jump: for $\phi=1_{[1,2]}$ one has $\Phi(s)=(2^s-1)/s$. (If $\phi$ is a Schwartz function with exponential decay, i.e. all $(t\partial_t)^k\phi$ decay faster than every power of $e^{-|\log t|}$, then $\Phi$ decays faster than every power of $|s|$ on vertical strips; cf. Proposition B.2.1.9 of the source.) In the source this lemma makes sense of the samples $\Phi\big((\log\chi(\theta)+2\pi i m)/\log\theta\big)$ in the Poisson summation formula with jump singularities (Proposition B.4.1.2), whose sum over $m$ is in general not absolutely convergent (Remark B.4.1.4).
--
--   **Formalization Note.** The function $\phi$ is represented by its logarithmic profile `g`, and $\Phi$ is `mellin (fun t => g (Real.log t))`, where Mathlib's `mellin f s` is $\int_0^\infty t^{s-1}f(t)\,dt$; absolute convergence is `MellinConvergent`. Hypothesis 1 is `ContDiffOn ℝ ∞ g Sᶜ` for a `Finset` `S`, together with the existence of the left and right limits of `iteratedDeriv j g` at the points of `S` (near a point of `S` the function `iteratedDeriv j g` is the genuine $j$-th derivative off `S`, because `Sᶜ` is open). The source also asks that $\phi$ and $(t\partial_t)\phi$ be bounded; this follows from 1 and 2 and is not a separate hypothesis. The values of `g` at the points of `S` are irrelevant.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 607-608, Lemma B.4.1.1, eqs. (B.4.1.1)-(B.4.1.3)

import Mathlib

open Filter Topology
open scoped Real ContDiff

set_option autoImplicit false

namespace ExplicitFormula

theorem mellin_entire_and_inv_bound_of_piecewise_smooth
    (g : ℝ → ℂ) (S : Finset ℝ)
    (hsmooth : ContDiffOn ℝ ∞ g (S : Set ℝ)ᶜ)
    (hlim : ∀ (j : ℕ) (x : ℝ), x ∈ S →
      (∃ l : ℂ, Tendsto (iteratedDeriv j g) (𝓝[<] x) (𝓝 l)) ∧
      (∃ r : ℂ, Tendsto (iteratedDeriv j g) (𝓝[>] x) (𝓝 r)))
    (hdecay : ∀ N : ℕ, ∃ C > (0 : ℝ), ∃ T > (0 : ℝ), ∀ x : ℝ, T < |x| →
      ‖g x‖ < C * Real.exp (-(N : ℝ) * |x|) ∧ ‖deriv g x‖ < C * Real.exp (-(N : ℝ) * |x|)) :
    (∀ s : ℂ, MellinConvergent (fun t : ℝ => g (Real.log t)) s) ∧
    Differentiable ℂ (mellin (fun t : ℝ => g (Real.log t))) ∧
    ∀ a b : ℝ, ∃ C > (0 : ℝ), ∃ R > (0 : ℝ), ∀ s : ℂ, a ≤ s.re → s.re ≤ b → R < ‖s‖ →
      ‖mellin (fun t : ℝ => g (Real.log t)) s‖ ≤ C / ‖s‖ := by sorry

end ExplicitFormula
