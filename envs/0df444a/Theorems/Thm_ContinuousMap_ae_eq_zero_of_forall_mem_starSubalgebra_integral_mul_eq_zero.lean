-- Prove2me | Theorems.Thm_ContinuousMap_ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero
-- name    : ContinuousMap.ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/23c195bb-ef20-541b-ab96-8cbc973899f6
-- title:
--   Vanishing a.e. against a point-separating star subalgebra
-- statement:
--   Let $X$ be a compact Hausdorff topological space equipped with its Borel $\sigma$-algebra, and let $\mu$ be a finite measure on $X$. Let $A$ be a $*$-subalgebra of the $\mathbb{C}$-algebra $C(X,\mathbb{C})$ of continuous complex-valued functions on $X$ (so $A$ contains the constants and is stable under pointwise products and under pointwise complex conjugation), and assume that $A$ separates the points of $X$: for any two distinct points of $X$ some element of $A$ takes different values at them. Let $\beta \in C(X,\mathbb{C})$, and suppose that $\int_X f(x)\,\beta(x)\,d\mu(x) = 0$ for every $f \in A$. The conclusion is that the underlying function $X \to \mathbb{C}$ of $\beta$ is equal to $0$ $\mu$-almost everywhere. (No separability or regularity hypothesis on $\mu$ is imposed beyond finiteness, and $A$ is not assumed closed in the uniform topology.)
--
--   This is the standard consequence of the complex Stone–Weierstrass theorem that a continuous function orthogonal to a point-separating $*$-subalgebra of $C(X,\mathbb{C})$ vanishes almost everywhere. In the formalisation it serves as the analytic input for statements about functions on compact groups annihilated by all $K$-finite test functions, and is used in the treatment of automorphic forms and in the Langlands–Tunnell part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ContinuousMap_ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero.lean

import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.RCLike.Lemmas

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory

theorem ContinuousMap.ae_eq_zero_of_forall_mem_starSubalgebra_integral_mul_eq_zero
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (A : StarSubalgebra ℂ C(X, ℂ)) (hA : A.SeparatesPoints)
    (β : C(X, ℂ))
    (h : ∀ f ∈ A, ∫ x, f x * β x ∂μ = 0) :
    (β : X → ℂ) =ᵐ[μ] 0 := by sorry
