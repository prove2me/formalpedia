-- Prove2me | Theorems.Thm_AutomorphicForm_IsTwistedOrbitalIntegralOn_unique_of_isRegularSemisimple_normString
-- name    : AutomorphicForm.IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/a2737736-eb1b-5bd5-a09f-0748944ad9b8
-- title:
--   Uniqueness of the twisted orbital integral at δ with regular semisimple norm
-- statement:
--   Let $K \subseteq L$ be a finite extension of fields, with $n = [L:K]$, and let $A$ be a commutative $K$-algebra carrying a Hausdorff, locally compact, second countable topological ring structure; the group $GL_2(L \otimes_K A)$ and all its subgroups are equipped with the Borel $\sigma$-algebra of their topologies. Let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma^{n} = 1$, acting on $L \otimes_K A$ through the first factor and hence on $GL_2(L \otimes_K A)$ entrywise, the resulting group endomorphism being written $\sigma$ again. Let $\mu$ be a Haar measure on $GL_2(L \otimes_K A)$, let $\delta \in GL_2(L \otimes_K A)$ be such that the norm string $N\delta = \delta\,\sigma(\delta)\cdots\sigma^{n-1}(\delta)$ has $\operatorname{tr}(N\delta)^2 - 4\det(N\delta)$ a unit of $L \otimes_K A$, let $\tau'$ be a Haar measure on the twisted centraliser $T = \{t : t\delta\sigma(t)^{-1} = \delta\}$, and let $\varphi \colon GL_2(L \otimes_K A) \to \mathbb{C}$ be Borel measurable and bounded in norm by some real constant. Suppose $I_1$ and $I_2$ are complex numbers each of which is of the form $\int \varphi(x^{-1}\delta\sigma(x))\,w(x)\,d\mu(x)$ for some non-negative Borel function $w$ of compact support satisfying $\int_{T} w(tx)\,d\tau'(t) = 1$ for every $x$ with $\varphi(x^{-1}\delta\sigma(x)) \ne 0$, the two witnesses $w$ being allowed to differ. Then $I_1 = I_2$.
--
--   This is the well-definedness of the $\sigma$-twisted orbital integral of $\varphi$ at $\delta$, realised as an integral over $GL_2(L \otimes_K A)$ against a section function for the twisted centraliser rather than as an integral over the quotient; it shows the predicate describing such integrals is single-valued. It is invoked throughout the local theory of twisted orbital integrals and their comparison with ordinary orbital integrals in the base change arguments, and cites the general identity [`MeasureTheory.integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one`](thm.html#MeasureTheory.integral_mul_eq_integral_mul_of_integral_subgroup_translate_eq_one) for two section functions attached to a closed subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsTwistedOrbitalIntegralOn_unique_of_isRegularSemisimple_normString.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.IsTwistedOrbitalIntegralOn.unique_of_isRegularSemisimple_normString
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (σ : L ≃ₐ[K] L) (hσ : σ ^ Module.finrank K L = 1)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (hμ : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] A)) _ _ (AutomorphicForm.glBorelOf (L ⊗[K] A)) μ)
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (hφm : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] A)] φ)
    (hφb : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C)
    {I₁ I₂ : ℂ} (h₁ : AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ I₁)
    (h₂ : AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ I₂) : I₁ = I₂ := by sorry
