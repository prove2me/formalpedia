-- Prove2me | Theorems.Thm_AutomorphicForm_exists_measurable_forall_integral_toTensorGL_diagUnits2_mul_diagUnits2_eq_one
-- name    : AutomorphicForm.exists_measurable_forall_integral_toTensorGL_diagUnits2_mul_diagUnits2_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/005c98c7-ad11-53ea-9de8-d2dde81432e6
-- title:
--   Existence of a normalised Borel weight on GL₂(L⊗_K K_∞)
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite extension of $K$ (so $L$ is a $K$-algebra and finite-dimensional over $K$), write $K_\infty$ for the infinite adele ring `InfiniteAdeleRing K`, and equip the unit group $K_\infty^\times$ with a measurable space structure that is the Borel structure of its topology; let $\nu_A$ be a Haar measure on $K_\infty^\times$. Put $E = L \otimes_K K_\infty$. The assertion is that there exists a function $\beta : GL_2(E) \to \mathbb{R}$ which is measurable for the $\sigma$-algebra [`AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)`](def/AutomorphicForm_TwistedOrbital.html#L57), that is, the Borel $\sigma$-algebra of the topology of $GL_2(E)$, which satisfies $\beta(x) \ge 0$ for all $x$, and which has the following normalisation: for every pair $a = (a_1, a_2)$ of units of $E$, the integral over $(p_1,p_2) \in K_\infty^\times \times K_\infty^\times$, with respect to the product measure $\nu_A \times \nu_A$, of $$\beta\bigl(\,\mathrm{diag}(1 \otimes p_1, 1 \otimes p_2)\cdot \mathrm{diag}(a_1,a_2)\,\bigr)$$ equals $1$. Here $\mathrm{diag}(x,y)$ denotes `diagUnits2 x y`, the invertible matrix $!![x,0;0,y]$ with its explicit diagonal inverse, and the map $\mathrm{diag}(p_1,p_2) \mapsto \mathrm{diag}(1 \otimes p_1, 1 \otimes p_2)$ is the group homomorphism [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71), obtained by applying the ring homomorphism underlying $\mathrm{Algebra.TensorProduct.includeRight} : K_\infty \to L \otimes_K K_\infty$ entrywise. Since the integral is a Bochner integral, the condition in particular forces integrability of each of these functions of $(p_1,p_2)$.
--
--   This is the existence of a Bruhat-type normalised weight (a "section weight") for the proper action of the diagonal torus $K_\infty^\times \times K_\infty^\times$ on the diagonal torus of $GL_2(L \otimes_K K_\infty)$, in the style of Bourbaki's construction of functions with prescribed total mass along the orbits of a proper group action. It feeds the archimedean estimates for twisted orbital integrals, being used in [`AutomorphicForm.exists_forall_prod_infinitePlace_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegralOn_tensorArch_scalar_mul`](thm.html#AutomorphicForm.exists_forall_prod_infinitePlace_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegralOn_tensorArch_scalar_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_measurable_forall_integral_toTensorGL_diagUnits2_mul_diagUnits2_eq_one.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_measurable_forall_integral_toTensorGL_diagUnits2_mul_diagUnits2_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ] (νA : Measure (InfiniteAdeleRing K)ˣ)
    [νA.IsHaarMeasure] :
    ∃ β : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ, Measurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] β ∧ (∀ x, 0 ≤ β x) ∧
      ∀ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ,
        ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
            β (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2) * diagUnits2 a.1 a.2)
          ∂(νA.prod νA) = 1 := by sorry
