-- Prove2me | Theorems.Thm_AutomorphicForm_exists_linearMap_resolvent_integral_comp_sigmaTensor_sub_mul_eq_integral_mul_comp_smul
-- name    : AutomorphicForm.exists_linearMap_resolvent_integral_comp_sigmaTensor_sub_mul_eq_integral_mul_comp_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/acfc6364-f7b1-5c7e-bf42-432d254631da
-- title:
--   Twisted resolvent and change of variables for y↦σ y-ry
-- statement:
--   Let $K\subseteq L$ be number fields with $L/K$ finite Galois, and let $\sigma\in\mathrm{Gal}(L/K)$ be such that every $\tau\in\mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma$, the degree $[L:K]$ being prime. Write $A=\mathrm{InfiniteAdeleRing}\,K$ and $E=L\otimes_K A$, equipped with a measurable space structure that is the Borel structure of its topology, and let $\lambda$ be an additive Haar measure on $E$. Let $\sigma_E=\sigma\otimes\mathrm{id}_A$ be the ring endomorphism [`AutomorphicForm.sigmaTensor`](def/AutomorphicForm_TwistedOrbital.html#L199) of $E$. Let $r\in E$ and let $c\in A^\times$ be a unit whose underlying element satisfies $c=1-N_{E/A}(r)$, the norm being `Algebra.norm` of the $A$-algebra $E$. Then there exists an $A$-linear map $M\colon E\to E$ which is continuous and satisfies: $\sigma_E(My)-r\,My=c\cdot y$ for all $y\in E$; $M(\sigma_E y-r\,y)=c\cdot y$ for all $y$; for every $g\colon E\to\mathbb{C}$, the function $y\mapsto g(\sigma_E y-r\,y)$ is $\lambda$-integrable if and only if $g$ is; and for all $F,G\colon E\to\mathbb{C}$,
--   $$\Bigl(\prod_{v\mid\infty}\|c_v\|^{\,v.\mathrm{mult}}\Bigr)\int_E F(\sigma_E y-r\,y)\,G(y)\,d\lambda(y)=\int_E F(y)\,G(c^{-1}\cdot My)\,d\lambda(y),$$
--   where $v$ runs over the infinite places of $K$, $c_v$ denotes the image `archEval K v c` of $c$ in the completion at $v$, and the real product is viewed as a complex scalar.
--
--   This is the change-of-variables statement for the twisted unipotent substitution $y\mapsto\sigma_E y-ry$ on $L\otimes_K K_\infty$, together with the existence of the twisted resolvent $M$ inverting it up to the factor $c=1-N(r)$; the Jacobian factor is the product of the archimedean absolute values of $c$ weighted by the multiplicities of the infinite places. It is used in the cyclic induction step of the Langlands–Tunnell argument, where it moves the substitution off the twisted logarithmic weight in the orbital-integral identity cited by [`AutomorphicForm.exists_linearMap_prod_norm_pow_mul_integral_comp_sigmaTensor_sub_mul_twistedLogWeight_eq_add_sum`](thm.html#AutomorphicForm.exists_linearMap_prod_norm_pow_mul_integral_comp_sigmaTensor_sub_mul_twistedLogWeight_eq_add_sum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_linearMap_resolvent_integral_comp_sigmaTensor_sub_mul_eq_integral_mul_comp_smul.lean

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
open scoped ENNReal Classical

theorem AutomorphicForm.exists_linearMap_resolvent_integral_comp_sigmaTensor_sub_mul_eq_integral_mul_comp_smul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (r : L ⊗[K] InfiniteAdeleRing K) (c : (InfiniteAdeleRing K)ˣ)
    (hc : (c : InfiniteAdeleRing K) = 1 - Algebra.norm (InfiniteAdeleRing K) r) :
    ∃ M : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K), Continuous M ∧
      (∀ y, AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (M y) - r * M y = (c : InfiniteAdeleRing K) • y) ∧
      (∀ y, M (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y) = (c : InfiniteAdeleRing K) • y) ∧
      (∀ g : (L ⊗[K] InfiniteAdeleRing K) → ℂ,
        Integrable (fun y => g (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y)) lam ↔ Integrable g lam) ∧
      ∀ F G : (L ⊗[K] InfiniteAdeleRing K) → ℂ,
        ((∏ v : NumberField.InfinitePlace K, ‖NumberField.AdelicLevel.archEval K v (c : InfiniteAdeleRing K)‖ ^ v.mult : ℝ) : ℂ) *
            ∫ y, F (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y) * G y ∂lam =
          ∫ y, F y * G (((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) • M y) ∂lam := by sorry
