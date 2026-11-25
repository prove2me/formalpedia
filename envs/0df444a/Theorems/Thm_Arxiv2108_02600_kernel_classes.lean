-- Prove2me | Theorems.Thm_Arxiv2108_02600_kernel_classes
-- name    : Arxiv2108_02600.kernel_classes
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T10:08:23.178983+00:00
-- url     : https://prove2.me/theorems/8607b5d7-0033-5b59-9125-0059db39f017
-- title:
--   Remark 4.2 and condition C3: $B\in C^n_{0,\pi}(\mathbb R^2)$, $C\in BC^n_{3/2}(\mathbb R^2)$
-- statement:
--   Let $\operatorname{Re}\eta>0$, $h<c$, $M>0$ and $n\ge1$. For every $f\in B^{(n)}_{c,M}$, the kernels $B$ and $C$ of (3.24)–(3.25), extended to the diagonal by continuity, satisfy, entrywise,
--
--   $$B\in C^n_{0,\pi}(\mathbb R^2),\qquad C\in BC^n_{3/2}(\mathbb R^2)\qquad\text{(Remark 4.2)}.$$
--
--   Moreover (condition C3), there is one constant $K$ such that for all $f\in B^{(n)}_{c,M}$, all $j+l\le n$ and all $|s-t|\ge\pi$, the kernel $A$ of $D-i\eta S$ satisfies
--
--   $$\Big|\frac{\partial^{j+l}A(s,t)}{\partial s^j\partial t^l}\Big|\le K(1+|s-t|)^{-3/2}.$$
--
--   **Formalization Note** "$C$ depends only on $M$" is read as: one constant serves the whole class $B^{(n)}_{c,M}$, with $\lambda,\mu,\omega,\eta,h,c,n$ fixed. Derivatives of order $\le n$ are measured by the norm of the iterated Fréchet derivative, which is equivalent to the maximum of the partial derivatives of that order.
-- source:
--   J. Li, X. Liu, B. Zhang and H. Zhang, The Nyström method for elastic wave scattering by unbounded rough surfaces, arXiv:2108.02600v1 (2021), claim c012; Section 4, proof of Theorem 4.1 (condition C3) and Remark 4.2, PDF p. 16

import Mathlib
import Definitions.Def_Arxiv2108_02600_Basic

open MeasureTheory Filter Topology

namespace Arxiv2108_02600

theorem kernel_classes (P : Lame) (η : ℂ) (hη : 0 < η.re) (h c M : ℝ) (hhc : h < c) (hM : 0 < M)
    (n : ℕ) (hn : 1 ≤ n) :
    (∀ f : ℝ → ℝ, InB n c M f → ∀ j k : Fin 2,
      IsC0pi n (fun p : ℝ × ℝ => kerB P η f p.1 p.2 j k) ∧
        IsBCnp n (3 / 2) (fun p : ℝ × ℝ => kerC P η h f p.1 p.2 j k)) ∧
    ∃ K : ℝ, ∀ f : ℝ → ℝ, InB n c M f → ∀ j k : Fin 2, ∀ m ≤ n, ∀ s t : ℝ, Real.pi ≤ |s - t| →
      ‖iteratedFDeriv ℝ m (fun p : ℝ × ℝ => kerA P η h f p.1 p.2 j k) (s, t)‖ ≤
        K * (1 + |s - t|) ^ (-(3 / 2 : ℝ)) := by sorry

end Arxiv2108_02600
