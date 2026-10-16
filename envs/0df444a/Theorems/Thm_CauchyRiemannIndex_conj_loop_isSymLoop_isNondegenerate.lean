-- Prove2me | Theorems.Thm_CauchyRiemannIndex_conj_loop_isSymLoop_isNondegenerate
-- name    : CauchyRiemannIndex.conj_loop_isSymLoop_isNondegenerate
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T10:11:12.574509+00:00
-- url     : https://prove2.me/theorems/94083dee-86e3-4132-9274-8ca6fdd6e7bd
-- title:
--   The complex-conjugated loop $-C\,S_\infty^{\mathsf T}C$ is a nondegenerate symmetric loop when $S_\infty$ is
-- statement:
--   Let $S_\infty:\mathbb R\to\mathbb R^{2n\times2n}$ be a continuous $1$-periodic loop of symmetric matrices whose asymptotic operator $A=-J_0\partial_t-S_\infty(t)$ is nondegenerate. Let $C=\begin{pmatrix}\mathrm{Id}&0\\0&-\mathrm{Id}\end{pmatrix}$ be complex conjugation on $\mathbb C^n=\mathbb R^{2n}$, and set
--   $$\bar S_\infty(t)=-C\,S_\infty(t)^{\mathsf T}\,C .$$
--   Then $\bar S_\infty$ is again a continuous $1$-periodic loop of symmetric matrices, and its asymptotic operator $-J_0\partial_t-\bar S_\infty(t)$ is nondegenerate.
--
--   The loop $\bar S_\infty$ is the asymptotic data of the conjugated formal adjoint $-C\,D_S^*\,C=D_{\bar S}$ of a Cauchy–Riemann operator $D_S=\partial_s+J_0\partial_t+S$ (Wendl, Lecture 4). The statement lets results proved under nondegeneracy hypotheses be applied to that adjoint operator.
--
--   **Formalization Note.** The loop hypothesis is `IsSymLoop` (continuous, $1$-periodic, symmetric values). Nondegeneracy is `IsNondegenerate`: $\det(1-\Psi(1))\ne0$ for every fundamental solution $\Psi'=J_0S_\infty\Psi$, $\Psi(0)=1$. $C$ is `conjMat n`, and $J_0$ is `Matrix.J`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 4, Lemma 4.17, Proposition 4.18 and Theorem 4.20, pp. 76-79

import Definitions.Def_CauchyRiemannIndex_Setting

namespace CauchyRiemannIndex

open Matrix

/-- If `S∞` is a loop of symmetric matrices whose asymptotic operator `-J₀ ∂ₜ - S∞` is
nondegenerate, then so is the conjugated loop `t ↦ -C S∞(t)ᵀ C`, where `C` is complex
conjugation on `ℂⁿ = ℝ²ⁿ`. -/
theorem conj_loop_isSymLoop_isNondegenerate (n : ℕ) (Sinf : ℝ → Mat n) (hS : IsSymLoop Sinf)
    (hnd : IsNondegenerate Sinf) :
    IsSymLoop (fun t => -(conjMat n * (Sinf t)ᵀ * conjMat n)) ∧
      IsNondegenerate (fun t => -(conjMat n * (Sinf t)ᵀ * conjMat n)) := by
  sorry

end CauchyRiemannIndex
