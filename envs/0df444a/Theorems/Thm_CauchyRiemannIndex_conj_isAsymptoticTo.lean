-- Prove2me | Theorems.Thm_CauchyRiemannIndex_conj_isAsymptoticTo
-- name    : CauchyRiemannIndex.conj_isAsymptoticTo
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T10:11:16.066379+00:00
-- url     : https://prove2.me/theorems/898f2305-efef-4a7c-a117-b017ef2650b9
-- title:
--   Complex conjugation $S\mapsto-C\,S^{\mathsf T}C$ preserves asymptotic convergence of Cauchy–Riemann coefficients
-- statement:
--   Let $S:\mathbb R\times\mathbb R\to\mathbb R^{2n\times2n}$ be continuous and $1$-periodic in $t$, and let $S^\pm$ be loops such that $S(s,\cdot)\to S^\pm$ entrywise and uniformly in $t$ as $s\to\pm\infty$. Let $C=\begin{pmatrix}\mathrm{Id}&0\\0&-\mathrm{Id}\end{pmatrix}$ be complex conjugation on $\mathbb C^n=\mathbb R^{2n}$, and set
--   $$\bar S(s,t)=-C\,S(s,t)^{\mathsf T}C,\qquad \bar S^\pm(t)=-C\,S^\pm(t)^{\mathsf T}C .$$
--   Then $\bar S$ is continuous and $1$-periodic in $t$, and $\bar S(s,\cdot)\to\bar S^\pm$ entrywise and uniformly in $t$ as $s\to\pm\infty$.
--
--   The coefficient $\bar S$ is that of the conjugated formal adjoint $D_{\bar S}=-C\,D_S^*\,C$ of $D_S=\partial_s+J_0\partial_t+S$ (Wendl, Lecture 4). The statement transfers the asymptotic hypothesis from $D_S$ to $D_{\bar S}$.
--
--   **Formalization Note.** Asymptotic convergence is `IsAsymptoticTo S Splus Sminus`: continuity, $t$-periodicity, and for each $\varepsilon>0$ an $R$ with $|S(s,t)_{ij}-S^\pm(t)_{ij}|\le\varepsilon$ for $\pm s\ge R$. $C$ is `conjMat n`. No symmetry of $S^\pm$ is assumed.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Lemma 4.17, Proposition 4.18 and Theorem 4.20, pp. 76-79

import Definitions.Def_CauchyRiemannIndex_Setting

namespace CauchyRiemannIndex

open Matrix

/-- If `S` is asymptotic to the loops `S±`, then the conjugated coefficient
`(s, t) ↦ -C S(s, t)ᵀ C` is asymptotic to the conjugated loops `t ↦ -C S±(t)ᵀ C`, where `C` is
complex conjugation on `ℂⁿ = ℝ²ⁿ`. -/
theorem conj_isAsymptoticTo (n : ℕ) (S : ℝ × ℝ → Mat n) (Splus Sminus : ℝ → Mat n)
    (hS : IsAsymptoticTo S Splus Sminus) :
    IsAsymptoticTo (fun x => -(conjMat n * (S x)ᵀ * conjMat n))
      (fun t => -(conjMat n * (Splus t)ᵀ * conjMat n))
      (fun t => -(conjMat n * (Sminus t)ᵀ * conjMat n)) := by
  sorry

end CauchyRiemannIndex
