-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_of_normString_eq_toTensorGL_scalar_of_algHom
-- name    : AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_of_normString_eq_toTensorGL_scalar_of_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/5d01c273-6eec-5322-9c54-95191c3fab73
-- title:
--   Continuous twisted section functions over a locally compact field
-- statement:
--   Let $L/K$ be a finite extension of fields whose degree $n=\operatorname{finrank}_K L$ is prime, and let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma\neq 1$. Let $A$ be a field equipped with a $K$-algebra structure and a topology making it a Hausdorff, locally compact, second-countable topological ring, and let $\iota\colon L\to A$ be a $K$-algebra homomorphism. Write $\mathrm{sigmaGL}$ for the automorphism of $\mathrm{GL}_2(L\otimes_K A)$ induced entrywise by the automorphism `sigmaTensor K L A σ` of $L\otimes_K A$. Let $\delta\in\mathrm{GL}_2(L\otimes_K A)$ and $z\in A^\times$ be such that the norm string $\prod_{i=0}^{n-1}\mathrm{sigmaGL}^{i}(\delta)$ (product in increasing order of $i$) equals the image of the scalar matrix $z\cdot 1$ under the map $\mathrm{GL}_2(A)\to\mathrm{GL}_2(L\otimes_K A)$ coming from $a\mapsto 1\otimes a$. Let $\varphi\colon\mathrm{GL}_2(L\otimes_K A)\to\mathbb{C}$ be continuous with compact support, and let $\tau'$ be a Haar measure on the twisted centraliser $T'_\delta=\{t: t\,\delta\,\mathrm{sigmaGL}(t)^{-1}=\delta\}$, taken with its Borel $\sigma$-algebra. Then there is a continuous $w\colon\mathrm{GL}_2(L\otimes_K A)\to\mathbb{R}$ which is nonnegative, Borel measurable, compactly supported, and satisfies $\int_{T'_\delta} w(tx)\,\mathrm{d}\tau'(t)=1$ for every $x$ with $\varphi(x^{-1}\delta\,\mathrm{sigmaGL}(x))\neq 0$.
--
--   This is the existence of a twisted section (Bruhat-type) function adapted to a $\sigma$-conjugacy class whose norm string is scalar, the device by which twisted orbital integrals attached to $\varphi$ are normalised over the twisted centraliser. It is the split-place model, valid for any locally compact field $A$ admitting a $K$-embedding of $L$ (so in particular for completions $K_v$, $\mathbb{R}$ and $\mathbb{C}$), and is used by [`AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime`](thm.html#AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_completion_of_isSigmaConjugate_scalar_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_of_normString_eq_toTensorGL_scalar_of_algHom.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_of_normString_eq_toTensorGL_scalar_of_algHom
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (A : Type) [Field A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (ι : L →ₐ[K] A)
    (δ : GL (Fin 2) (L ⊗[K] A)) (z : Aˣ)
    (hδ : normString K L A σ δ = toTensorGL K L A (Matrix.GeneralLinearGroup.scalar (Fin 2) z))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ') :
    ∃ w : GL (Fin 2) (L ⊗[K] A) → ℝ, IsTwistedSectionFnOn K L A σ δ τ' φ w ∧ Continuous w := by sorry
