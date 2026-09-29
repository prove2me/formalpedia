-- Prove2me | Theorems.Thm_AutomorphicForm_contDiff_splitFibreIntegral_psiGL_real
-- name    : AutomorphicForm.contDiff_splitFibreIntegral_psiGL_real
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/1e1e5dcc-255c-55c6-a2f9-d99e8ea0b582
-- title:
--   Smoothness and compact support of the split fibre integral over ℝ
-- statement:
--   Let $K$ and $L$ be fields with $L$ a finite-dimensional $K$-algebra, let $\ell = \operatorname{finrank}_K L$ be prime, and let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma \neq 1$. Fix a $K$-algebra structure on $\mathbb{R}$ and a $K$-algebra map $\iota : L \to \mathbb{R}$, and let $\mu_A$ be a Haar measure on $\mathrm{GL}_2(\mathbb{R})$ for the Borel $\sigma$-algebra `glBorelOf ℝ` of its topology. Let $\varphi : \mathrm{GL}_2(L \otimes_K \mathbb{R}) \to \mathbb{C}$ be assumed to have compact support and to be of the form $\varphi(g) = \Phi\big((\text{entries of the }k\text{-th component of } \mathrm{psiGL}(g))_{k < \ell}\big)$ for some $C^\infty$ function $\Phi$ on $\mathrm{Fin}\,\ell \to \mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to \mathbb{R}$, where `SplitPlace.psiGL` is the multiplicative isomorphism $\mathrm{GL}_2(L \otimes_K \mathbb{R}) \cong \mathrm{GL}_2(\mathbb{R})^{\ell}$ induced by the $K$-algebra isomorphism $L \otimes_K \mathbb{R} \cong \mathbb{R}^{\ell}$ attached to $\sigma$ and $\iota$. Then the function $h \mapsto \int_{\mathrm{GL}_2(\mathbb{R})^{\ell-1}} \varphi\big(\mathrm{coords}^{-1}(g, (\prod_k g_k)^{-1} h)\big)\, d\mu_A^{\otimes(\ell-1)}(g)$, namely `splitFibreIntegral`, is likewise given by a $C^\infty$ function of the matrix entries of $h \in \mathrm{GL}_2(\mathbb{R})$ and has compact support.
--
--   This is the archimedean smoothness-and-support statement for the fibre (twisted transfer) integral along the split coordinates of $L \otimes_K \mathbb{R}$: a smooth compactly supported test function on $\mathrm{GL}_2(L \otimes_K \mathbb{R}) \cong \mathrm{GL}_2(\mathbb{R})^{\ell}$ pushes forward, under integration over the first $\ell-1$ coordinates with the last adjusted so that the product equals $h$, to a smooth compactly supported test function on $\mathrm{GL}_2(\mathbb{R})$. It is used in the derivation of orbital-integral identities for the resulting test function at real places, by [`AutomorphicForm.isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_real_of_nhds_forall_isRegularSemisimple`](thm.html#AutomorphicForm.isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_real_of_nhds_forall_isRegularSemisimple).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_contDiff_splitFibreIntegral_psiGL_real.lean

import Definitions.Def_AutomorphicForm_SplitFibreIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions NNReal

theorem AutomorphicForm.contDiff_splitFibreIntegral_psiGL_real
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    [Algebra K ℝ] (ι : L →ₐ[K] ℝ)
    (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
    (φ : GL (Fin 2) (L ⊗[K] ℝ) → ℂ)
    (hφ : (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun k i j =>
        ((SplitPlace.psiGL ℝ σ ι hdeg hσ g k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
      HasCompactSupport φ) :
    (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, splitFibreIntegral K L hdeg σ hσ ℝ ι μA φ g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
    HasCompactSupport (splitFibreIntegral K L hdeg σ hσ ℝ ι μA φ) := by sorry
