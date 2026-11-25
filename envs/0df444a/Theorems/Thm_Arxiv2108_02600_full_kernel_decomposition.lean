-- Prove2me | Theorems.Thm_Arxiv2108_02600_full_kernel_decomposition
-- name    : Arxiv2108_02600.full_kernel_decomposition
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:57:08.980342+00:00
-- url     : https://prove2.me/theorems/3eaabacf-a268-4b35-b1d1-02406399956a
-- title:
--   Eqs. (3.21)–(3.23): the kernel of $D-i\eta S$ and its logarithmic splitting
-- statement:
--   Let $\operatorname{Re}\eta>0$, $h<c$, $M>0$ and $f\in B^{(n)}_{c,M}$, so that $\Gamma$ lies above the line $x_2=h$. Let $A(s,t)=2[\Pi^{(2)}_{D,h}(x(s),y(t))-i\eta G_{D,h}(x(s),y(t))]\sqrt{1+f'(t)^2}$. Then:
--
--   1. for every bounded continuous $\psi$ and every $s$, the integrands of $D\psi(s)$, $S\psi(s)$ and $\int A(s,t)\psi(t)\,dt$ are absolutely integrable, and $[(D-i\eta S)\psi](s)=\int_{\mathbb R}A(s,t)\psi(t)\,dt$ (3.21);
--   2. for $s\ne t$, $A=-i\eta A^{(1)}+A^{(2)}-A^{(3)}$. Here $A^{(3)}=2\{[P^{(y)}(G_{j\cdot}(x,y')-U_{j\cdot}(x,y))^\top]_k-i\eta(G_{jk}(x,y')-U_{jk}(x,y))\}\sqrt{1+f'(t)^2}$ is the kernel of $D_2-i\eta S_2$ from (3.3), (3.5) and (3.6);
--   3. for $s\ne t$, $A=B^*\ln|s-t|+C^*$, with $B^*=-i\eta B^{(1)}+B^{(2)}$ (3.22) and $C^*=-i\eta C^{(1)}+C^{(2)}-A^{(3)}$ (3.23).
--
--   **Formalization Note** $A^{(3)}$ is built from $U(x,y)$, as in (3.5)–(3.6) and the decomposition $G_{D,h}=G(x,y)-G(x,y')+U(x,y)$. The printed formula (3.20) for $A^{(5)}$ uses $U(x,y')$ instead. Item 1 states explicitly the absolute convergence of the three integrals that (3.21) presupposes, so neither side can take a default value.
-- source:
--   J. Li, X. Liu, B. Zhang and H. Zhang, The Nyström method for elastic wave scattering by unbounded rough surfaces, arXiv:2108.02600v1 (2021), claim c019; Section 3, eqs. (3.21)-(3.23) with (2.13)-(2.14), (3.2)-(3.6), PDF pp. 7-8, 12-13

import Mathlib
import Definitions.Def_Arxiv2108_02600_Basic

open MeasureTheory Filter Topology

namespace Arxiv2108_02600

theorem full_kernel_decomposition (P : Lame) (η : ℂ) (hη : 0 < η.re) (h c M : ℝ) (hhc : h < c)
    (hM : 0 < M) (n : ℕ) (f : ℝ → ℝ) (hf : InB n c M f) :
    (∀ psi : ℝ → Fin 2 → ℂ, IsBC psi → ∀ s : ℝ,
      (∀ j : Fin 2,
        Integrable (fun t => (∑ k, piKernel P (greenDH P h) (normal f t) (surfPt f s) (surfPt f t) j k *
          psi t k) * (jac f t : ℂ)) ∧
        Integrable (fun t => (∑ k, greenDH P h (surfPt f s) (surfPt f t) j k * psi t k) * (jac f t : ℂ)) ∧
        Integrable (fun t => ∑ k, kerA P η h f s t j k * psi t k)) ∧
      opD P h f psi s - (Complex.I * η) • opS P h f psi s =
        fun j => ∫ t : ℝ, ∑ k, kerA P η h f s t j k * psi t k) ∧
    ∀ s t : ℝ, s ≠ t →
      kerA P η h f s t = (-(Complex.I * η)) • kerA1 P f s t + kerA2 P f s t - kerA3 P η h f s t ∧
      kerA P η h f s t = (Real.log |s - t| : ℂ) • kerBstar P η f s t + kerCstar P η h f s t := by sorry

end Arxiv2108_02600
