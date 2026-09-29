-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isSigmaConjugate_scalar_of_coupled
-- name    : AutomorphicForm.exists_isSigmaConjugate_scalar_of_coupled
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/9e19ebb5-e2cb-563a-8838-3294a9494331
-- title:
--   Coupled measures force σ-conjugacy of δ to a scalar
-- statement:
--   Let $K \subseteq L$ be fields with $L$ a finite-dimensional $K$-algebra, let $\sigma$ be a $K$-algebra automorphism of $L$, and let $A$ be a commutative $K$-algebra equipped with a Hausdorff topology making it a topological ring. Write $\sigma$ also for the induced automorphism $\sigma \otimes \mathrm{id}$ of $L \otimes_K A$ and for its entrywise action `sigmaGL` on $GL_2(L \otimes_K A)$, and let $g \mapsto 1 \otimes g$ denote the entrywise map `toTensorGL` $: GL_2(A) \to GL_2(L \otimes_K A)$. Let $\gamma \in GL_2(A)$ be assumed scalar, i.e. $\gamma = c \cdot 1$ for some unit $c$ of $A$, and let $\delta, y \in GL_2(L \otimes_K A)$. Let $\tau$ be a measure on the centralizer of $\{\gamma\}$ in $GL_2(A)$ and $\tau'$ a measure on the twisted centralizer $\{t \in GL_2(L \otimes_K A) : t\,\delta\,\sigma(t)^{-1} = \delta\}$, both subgroups carrying the Borel $\sigma$-algebra of the subspace topology. Assume $\tau$ gives positive mass to every non-empty open set, and that the pair is coupled through $y$: the pushforward of $\tau'$ along $t \mapsto y^{-1} t y$ equals the pushforward of $\tau$ along $t \mapsto 1 \otimes t$, as Borel measures on $GL_2(L \otimes_K A)$. Then there is a unit $d$ of $L \otimes_K A$ and an $x \in GL_2(L \otimes_K A)$ with $d \cdot 1 = x^{-1}\,\delta\,\sigma(x)$.
--
--   This is the rigidity step in the comparison of orbital integrals on $GL_2(A)$ with twisted orbital integrals on $GL_2(L \otimes_K A)$ in the style of Langlands' base change for $GL(2)$: a centralizer measure of full support, coupled through $y$ to a measure on the twisted centralizer of $\delta$, pins $\delta$ down to the $\sigma$-conjugacy class of a scalar. It is used, typically in contrapositive form, by the semilocal central transfer peeling steps and by the evaluation of a twisted orbital integral as a signed multiple of an orbital integral at a scalar.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isSigmaConjugate_scalar_of_coupled.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open scoped TensorProduct

theorem AutomorphicForm.exists_isSigmaConjugate_scalar_of_coupled
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) (A : Type) [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A]
    (γ : GL (Fin 2) A) (hγ : ∃ c : Aˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (δ y : GL (Fin 2) (L ⊗[K] A))
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (AutomorphicForm.centralizerBorel A γ))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (hτ : @Measure.IsOpenPosMeasure _ _ (AutomorphicForm.centralizerBorel A γ) τ)
    (hc : AutomorphicForm.Coupled K L A σ γ δ y τ τ') :
    ∃ d : (L ⊗[K] A)ˣ, AutomorphicForm.IsSigmaConjugate K L A σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) d) := by sorry
