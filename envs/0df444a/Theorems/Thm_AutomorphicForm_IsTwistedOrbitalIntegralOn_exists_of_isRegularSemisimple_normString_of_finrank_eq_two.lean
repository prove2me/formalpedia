-- Prove2me | Theorems.Thm_AutomorphicForm_IsTwistedOrbitalIntegralOn_exists_of_isRegularSemisimple_normString_of_finrank_eq_two
-- name    : AutomorphicForm.IsTwistedOrbitalIntegralOn.exists_of_isRegularSemisimple_normString_of_finrank_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/4d7cd85a-3a80-5c8a-b284-3d8c528adbd9
-- title:
--   Existence of twisted orbital integrals at regular semisimple norms
-- statement:
--   Let $K$ be a field of characteristic zero, $L$ a finite extension field of $K$ with $\operatorname{finrank}_K L = 2$, and $\sigma$ a $K$-algebra automorphism of $L$ such that every $K$-algebra automorphism $\tau$ of $L$ lies in the subgroup of integer powers of $\sigma$. Let $A$ be a field that is a $K$-algebra, carrying a topology making it a Hausdorff, locally compact, second countable topological ring, and put $E = L \otimes_K A$ with the algebra and topology given by the right-action tensor instances in scope. Write $\sigma_{GL}$ for the endomorphism `sigmaGL K L A σ` of $GL_2(E)$, namely entrywise application of `sigmaTensor K L A σ`. Let $\mu$ be any measure on $GL_2(E)$ for its Borel $\sigma$-algebra, and let $\delta \in GL_2(E)$ be such that the norm string $N\delta = \prod_{i<2}\sigma_{GL}^{i}(\delta) = \delta\,\sigma_{GL}(\delta)$ is regular semisimple, i.e. $\operatorname{tr}(N\delta)^2 - 4\det(N\delta)$ is a unit of $E$. Let $\tau'$ be a Haar measure, for the Borel $\sigma$-algebra, on the twisted centralizer $T = \{t \in GL_2(E) : t\,\delta\,\sigma_{GL}(t)^{-1} = \delta\}$, and let $\varphi : GL_2(E) \to \mathbb{C}$ have compact support. Then there is a complex number $I$ which is a twisted orbital integral of $\varphi$ at $\delta$ relative to $\mu$ and $\tau'$: that is, there is a function $w : GL_2(E) \to \mathbb{R}$ which is nonnegative, Borel measurable and compactly supported, satisfies $\int_T w(tx)\,d\tau'(t) = 1$ for every $x$ with $\varphi(x^{-1}\delta\,\sigma_{GL}(x)) \neq 0$, and for which $I = \int_{GL_2(E)} \varphi(x^{-1}\delta\,\sigma_{GL}(x))\,w(x)\,d\mu(x)$.
--
--   This is the existence half of the assertion that the twisted orbital integral of a compactly supported test function at an element with regular semisimple norm is a well-defined number, in the form used for quadratic base change for $GL_2$: the section function $w$ replaces integration over the quotient $T \backslash GL_2(E)$ by integration against $\mu$. It is invoked in the construction of elliptic transport and straightening for twisted conjugacy classes of non-scalar type in [`AutomorphicForm.exists_ellipticTransport_coupled_straighten_of_not_isSigmaConjugate_scalar_of_finrank_eq_two`](thm.html#AutomorphicForm.exists_ellipticTransport_coupled_straighten_of_not_isSigmaConjugate_scalar_of_finrank_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsTwistedOrbitalIntegralOn_exists_of_isRegularSemisimple_normString_of_finrank_eq_two.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.IsTwistedOrbitalIntegralOn.exists_of_isRegularSemisimple_normString_of_finrank_eq_two
    (K L : Type) [Field K] [CharZero K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (A : Type) [Field A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    [LocallyCompactSpace A] [SecondCountableTopology A]
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (δ : GL (Fin 2) (L ⊗[K] A))
    (hδ : AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L A σ δ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ) τ')
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ I : ℂ, AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ I := by sorry
