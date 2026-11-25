-- Prove2me | Theorems.Thm_Arxiv2108_02600_kernel_log_sine_form
-- name    : Arxiv2108_02600.kernel_log_sine_form
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T10:01:16.431964+00:00
-- url     : https://prove2.me/theorems/adfe1c2d-ec1e-55d7-b9ba-906fc54b5351
-- title:
--   Eqs. (3.1), (3.24)–(3.25): the kernel in the form $\frac{1}{2\pi}B\ln(4\sin^2\frac{s-t}{2})+C$
-- statement:
--   Let $A,B^*,C^*:\mathbb R^2\to\mathbb C^{2\times2}$ satisfy $A(s,t)=B^*(s,t)\ln|s-t|+C^*(s,t)$ for $s\ne t$. Let $\chi$ be the cut-off of Section 3: $\chi(s)=1$ for $|s|\le1$, $\chi(s)=[1+\exp(\frac1{\pi-|s|}+\frac1{1-|s|})]^{-1}$ for $1<|s|<\pi$, $\chi(s)=0$ for $|s|\ge\pi$. Define (3.24)–(3.25)
--
--   $$B(s,t)=\pi B^*(s,t)\chi(s-t),\qquad C(s,t)=B^*(s,t)\Big[(1-\chi(s-t))\ln|s-t|-\chi(s-t)\ln\frac{\sin\frac{s-t}2}{\frac{s-t}2}\Big]+C^*(s,t).$$
--
--   Then for $s\ne t$
--
--   $$A(s,t)=\frac1{2\pi}B(s,t)\ln\Big(4\sin^2\frac{s-t}2\Big)+C(s,t)\qquad(3.1),$$
--
--   and on the diagonal $B(s,s)=\pi B^*(s,s)$ and $C(s,s)=C^*(s,s)$, in the following sense. If $B^*(s,t)\to L_B$ and $C^*(s,t)\to L_C$ as $t\to s$, then $B(s,t)\to\pi L_B$ and $C(s,t)\to L_C$.
--
--   **Formalization Note** The statement is proved for arbitrary kernels with a logarithmic splitting. The paper's kernel is the case $A$ = kernel of $D-i\eta S$, $B^*=-i\eta B^{(1)}+B^{(2)}$, $C^*=-i\eta C^{(1)}+C^{(2)}-A^{(3)}$ (see `full_kernel_decomposition`). Diagonal values are expressed as limits. Where $\sin\frac{s-t}2=0$ we have $|s-t|\ge2\pi$, so $\chi=0$ and both sides reduce to $B^*\ln|s-t|+C^*$.
-- source:
--   J. Li, X. Liu, B. Zhang and H. Zhang, The Nyström method for elastic wave scattering by unbounded rough surfaces, arXiv:2108.02600v1 (2021), claim c009; Section 3, eqs. (3.1), (3.24), (3.25) and the diagonal values after (3.25), PDF pp. 7, 13

import Mathlib
import Definitions.Def_Arxiv2108_02600_Basic

open MeasureTheory Filter Topology

namespace Arxiv2108_02600

theorem kernel_log_sine_form (A Bs Cs : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ)
    (hA : ∀ s t : ℝ, s ≠ t → A s t = (Real.log |s - t| : ℂ) • Bs s t + Cs s t) :
    let B : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun s t =>
      ((Real.pi * cutoff (s - t) : ℝ) : ℂ) • Bs s t
    let C : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ := fun s t =>
      (((1 - cutoff (s - t)) * Real.log |s - t| -
          cutoff (s - t) * Real.log (Real.sin ((s - t) / 2) / ((s - t) / 2)) : ℝ) : ℂ) • Bs s t +
        Cs s t
    (∀ s t : ℝ, s ≠ t →
      A s t = ((1 / (2 * Real.pi) * Real.log (4 * Real.sin ((s - t) / 2) ^ 2) : ℝ) : ℂ) • B s t +
        C s t) ∧
    ∀ (s : ℝ) (Lb Lc : Matrix (Fin 2) (Fin 2) ℂ),
      Tendsto (Bs s) (𝓝[≠] s) (𝓝 Lb) → Tendsto (Cs s) (𝓝[≠] s) (𝓝 Lc) →
        Tendsto (B s) (𝓝[≠] s) (𝓝 ((Real.pi : ℂ) • Lb)) ∧ Tendsto (C s) (𝓝[≠] s) (𝓝 Lc) := by sorry

end Arxiv2108_02600
