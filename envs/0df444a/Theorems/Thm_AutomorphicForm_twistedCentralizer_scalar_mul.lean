-- Prove2me | Theorems.Thm_AutomorphicForm_twistedCentralizer_scalar_mul
-- name    : AutomorphicForm.twistedCentralizer_scalar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/0af2879d-4715-58f1-a9a4-132d6c19ef50
-- title:
--   Central translates do not change the twisted centraliser
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, finite-dimensional over $K$, let $A$ be a commutative topological $K$-algebra, and write $E = L \otimes_K A$ for the base change, on which a $K$-algebra automorphism $\sigma$ of $L$ acts through the first tensor factor; the induced map on $\mathrm{GL}_2(E)$, entrywise application of this action, is the group homomorphism [`AutomorphicForm.sigmaGL K L A σ`](def/AutomorphicForm_TwistedOrbital.html#L202). For $\delta \in \mathrm{GL}_2(E)$ the subgroup [`AutomorphicForm.twistedCentralizer K L A σ δ`](def/AutomorphicForm_TwistedOrbital.html#L220) is by definition the $\sigma$-centraliser $\{\, t \in \mathrm{GL}_2(E) : t\,\delta\,\sigma(t)^{-1} = \delta \,\}$, where $\sigma(t)$ denotes the image of $t$ under `sigmaGL`. The assertion is that for every unit $c \in E^{\times}$, with $\mathrm{scalar}(c) = c \cdot 1_2$ the corresponding scalar element of $\mathrm{GL}_2(E)$, and every $\delta \in \mathrm{GL}_2(E)$, the two subgroups of $\mathrm{GL}_2(E)$ given by the $\sigma$-centraliser of $\mathrm{scalar}(c)\,\delta$ and the $\sigma$-centraliser of $\delta$ are equal. Note that $\sigma$ is applied to $t$ only, so no compatibility of $c$ with $\sigma$ is required.
--
--   This is the elementary invariance of the $\sigma$-twisted centraliser (the stabiliser for $\sigma$-conjugacy, the torus occurring in twisted orbital integrals) under multiplying the element $\delta$ by a central scalar. It is used where a central translate is absorbed into the twisted orbital integral, in the statements on twisted weighted orbital integrals at scalar multiples of diagonal units and at archimedean places that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_twistedCentralizer_scalar_mul.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.twistedCentralizer_scalar_mul
    (K L A : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommRing A] [Algebra K A] [TopologicalSpace A]
    (σ : L ≃ₐ[K] L) (c : (L ⊗[K] A)ˣ) (δ : GL (Fin 2) (L ⊗[K] A)) :
    AutomorphicForm.twistedCentralizer K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ) =
      AutomorphicForm.twistedCentralizer K L A σ δ := by sorry
