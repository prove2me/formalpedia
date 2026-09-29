-- Prove2me | Theorems.Thm_AutomorphicForm_map_mul_sigmaTensor_sub_mul_addHaar_infiniteAdeleRing_eq_inv_prod_norm_archEval_algebraNorm_sub_pow_mult_smul
-- name    : AutomorphicForm.map_mul_sigmaTensor_sub_mul_addHaar_infiniteAdeleRing_eq_inv_prod_norm_archEval_algebraNorm_sub_pow_mult_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/462ab096-7392-5f46-8522-9082e4aa635b
-- title:
--   Archimedean module of y ↦ aσ(y) - by on L ⊗_K K_∞
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ finite and Galois, let $\sigma$ be a $K$-automorphism of $L$ such that every $K$-automorphism of $L$ lies in the subgroup of integer powers of $\sigma$, and assume the degree $[L:K]$ is prime. Write $E = L \otimes_K \mathbb{A}_{K,\infty}$ for the base change of $L$ to the infinite adele ring of $K$, equipped with a measurable space structure that is the Borel structure of its topology, and let $\lambda$ be an additive Haar measure on $E$. Let $a, b \in E$ and suppose that $N(a) - N(b)$ is a unit of $\mathbb{A}_{K,\infty}$, where $N$ denotes the algebra norm of $E$ over $\mathbb{A}_{K,\infty}$. Put $c = \prod_{w} \lVert (N(a)-N(b))_w \rVert^{w.\mathrm{mult}}$, the product over the infinite places $w$ of $K$ of the $w$-component of $N(a)-N(b)$, evaluated in the completion $K_w$ via the evaluation ring homomorphism [`NumberField.AdelicLevel.archEval`](def/NumberField_AdelicLevel.html#L137), normed and raised to the power $w.\mathrm{mult}$. Then two things hold: first, the pushforward of $\lambda$ along $y \mapsto a\,(\sigma \otimes \mathrm{id})(y) - b\,y$ equals $c^{-1} \cdot \lambda$ (the scalar taken in $[0,\infty]$); second, for every function $g : E \to \mathbb{C}$, with no measurability or integrability hypothesis, $\int g(a\,(\sigma \otimes \mathrm{id})(y) - b\,y)\,d\lambda(y) = c^{-1} \int g\,d\lambda$.
--
--   This is the archimedean computation of the module (Jacobian factor) of the twisted map $y \mapsto a\,\sigma(y) - by$ on $L \otimes_K K_\infty$, the change-of-variables identity needed when twisted orbital integrals over the archimedean places are manipulated. It is used in the construction of test functions and of resolvent-type integral identities for twisted orbital integrals in the base-change comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_map_mul_sigmaTensor_sub_mul_addHaar_infiniteAdeleRing_eq_inv_prod_norm_archEval_algebraNorm_sub_pow_mult_smul.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem AutomorphicForm.map_mul_sigmaTensor_sub_mul_addHaar_infiniteAdeleRing_eq_inv_prod_norm_archEval_algebraNorm_sub_pow_mult_smul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (a b : (L ⊗[K] InfiniteAdeleRing K))
    (hab : IsUnit (Algebra.norm (InfiniteAdeleRing K) a - Algebra.norm (InfiniteAdeleRing K) b)) :
    Measure.map (fun y : (L ⊗[K] InfiniteAdeleRing K) => a * AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - b * y) lam =
        ENNReal.ofReal ((∏ w : NumberField.InfinitePlace K, ‖NumberField.AdelicLevel.archEval K w (Algebra.norm (InfiniteAdeleRing K) a - Algebra.norm (InfiniteAdeleRing K) b)‖ ^ w.mult)⁻¹) • lam ∧
    ∀ g : (L ⊗[K] InfiniteAdeleRing K) → ℂ,
      ∫ y, g (a * AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - b * y) ∂lam =
        (((∏ w : NumberField.InfinitePlace K, ‖NumberField.AdelicLevel.archEval K w (Algebra.norm (InfiniteAdeleRing K) a - Algebra.norm (InfiniteAdeleRing K) b)‖ ^ w.mult)⁻¹ : ℝ) : ℂ) * ∫ y, g y ∂lam := by sorry
