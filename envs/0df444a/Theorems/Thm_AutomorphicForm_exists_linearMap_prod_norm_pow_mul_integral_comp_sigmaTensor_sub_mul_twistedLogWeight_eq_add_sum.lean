-- Prove2me | Theorems.Thm_AutomorphicForm_exists_linearMap_prod_norm_pow_mul_integral_comp_sigmaTensor_sub_mul_twistedLogWeight_eq_add_sum
-- name    : AutomorphicForm.exists_linearMap_prod_norm_pow_mul_integral_comp_sigmaTensor_sub_mul_twistedLogWeight_eq_add_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/c6b101b2-dac7-568d-bee0-103fa57d16f1
-- title:
--   Splitting the archimedean twisted log-weighted integral
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ finite Galois, let $\sigma \in \operatorname{Gal}(L/K)$ be such that every element of the Galois group lies in the subgroup of integer powers of $\sigma$, and suppose $[L:K]$ is prime. Put $E := L \otimes_K K_\infty$, where $K_\infty$ is the infinite adele ring of $K$, equipped with a measurable structure that is the Borel structure of its topology and with an additive Haar measure $\lambda$. Let $w$ be an infinite place of $K$, let $r \in E$, and let $c \in K_\infty^{\times}$ satisfy $c = 1 - N_{E/K_\infty}(r)$. Let $\Psi$ be a continuous, compactly supported complex function on the mixed space of $L$. Write $\sigma_E$ for the ring endomorphism of $E$ obtained from $\sigma$ on $L$ and the identity on $K_\infty$, write $\iota$ for the composite of the isomorphism $E \cong K_\infty \otimes_K L \cong L_\infty$ coming from the infinite-place data with the identification of $L_\infty$ with the mixed space, and for an infinite place $w'$ of $L$ write $y_{w'}$ for the component at $w'$ in $w'$-completion of the infinite adele attached to $y$, and similarly $c_v$ for $v$ an infinite place of $K$. Then there is a $K_\infty$-linear map $M : E \to E$ which is continuous, satisfies $\sigma_E(M y) - r\,M y = c \cdot y$ and $M(\sigma_E y - r y) = c \cdot y$ for all $y \in E$, and is such that: the function $y \mapsto \Psi(\iota(\sigma_E y - r y)) \cdot \sum_{w' \mid w} m_{w'} \log(1 + \lVert y_{w'}\rVert^2)$ (the sum over infinite places $w'$ of $L$ restricting to $w$, with $m_{w'}$ the local multiplicity) is $\lambda$-integrable; $y \mapsto \Psi(\iota y)$ is $\lambda$-integrable; for every infinite place $w'$ of $L$ the function $y \mapsto \Psi(\iota y)\log(\lVert c_w\rVert^2 + \lVert (My)_{w'}\rVert^2)$ is $\lambda$-integrable; and $$\Big(\prod_{v} \lVert c_v\rVert^{m_v}\Big)\int_E \Psi(\iota(\sigma_E y - r y))\sum_{w'\mid w} m_{w'}\log\big(1+\lVert y_{w'}\rVert^2\big)\,d\lambda = -2[L:K]\,m_w \log\lVert c_w\rVert \int_E \Psi(\iota y)\,d\lambda + \sum_{w'\mid w} m_{w'}\int_E \Psi(\iota y)\log\big(\lVert c_w\rVert^2 + \lVert (My)_{w'}\rVert^2\big)\,d\lambda,$$ the product being over all infinite places $v$ of $K$.
--
--   This is the archimedean twisted weighted orbital integral computation at a single place $w$ of $K$: the logarithmic weight attached to $w$, transported through the twisted operator $\sigma_E - r$, splits into a main term proportional to $\log\lVert c_w\rVert$ and regular logarithmic potentials indexed by the places of $L$ above $w$, with the resolvent $M$ of $\sigma_E - r$ providing the change of variables. It is used in the real-place and complex-place versions of the same identity for smooth compactly supported test functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_linearMap_prod_norm_pow_mul_integral_comp_sigmaTensor_sub_mul_twistedLogWeight_eq_add_sum.lean

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

theorem AutomorphicForm.exists_linearMap_prod_norm_pow_mul_integral_comp_sigmaTensor_sub_mul_twistedLogWeight_eq_add_sum
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (w : NumberField.InfinitePlace K)
    (r : L ⊗[K] InfiniteAdeleRing K) (c : (InfiniteAdeleRing K)ˣ)
    (hc : (c : InfiniteAdeleRing K) = 1 - Algebra.norm (InfiniteAdeleRing K) r)
    (Ψ : NumberField.mixedEmbedding.mixedSpace L → ℂ) (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) :
    ∃ M : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K), Continuous M ∧
      (∀ y, AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (M y) - r * M y = (c : InfiniteAdeleRing K) • y) ∧
      (∀ y, M (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y) = (c : InfiniteAdeleRing K) • y) ∧
      Integrable (fun y : L ⊗[K] InfiniteAdeleRing K =>
        Ψ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y))) * (((∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
            (w'.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (y))‖ ^ 2)) : ℝ) : ℂ)) lam ∧
      Integrable (fun y : L ⊗[K] InfiniteAdeleRing K => Ψ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y)))) lam ∧
      (∀ w' : NumberField.InfinitePlace L, Integrable (fun y : L ⊗[K] InfiniteAdeleRing K =>
        Ψ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))) *
          (Real.log (‖NumberField.AdelicLevel.archEval K w (c : InfiniteAdeleRing K)‖ ^ 2 +
            ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (M y))‖ ^ 2) : ℂ)) lam) ∧
      ((∏ v : NumberField.InfinitePlace K,
          ‖NumberField.AdelicLevel.archEval K v (c : InfiniteAdeleRing K)‖ ^ v.mult : ℝ) : ℂ) *
        ∫ y, Ψ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y))) * (((∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
            (w'.mult : ℝ) * Real.log (1 + ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (y))‖ ^ 2)) : ℝ) : ℂ) ∂lam =
      -2 * (Module.finrank K L : ℂ) *
          (((w.mult : ℝ) * Real.log ‖NumberField.AdelicLevel.archEval K w (c : InfiniteAdeleRing K)‖ : ℝ) : ℂ) *
          ∫ y, Ψ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))) ∂lam +
        ∑ w' ∈ Finset.univ.filter (fun w' : NumberField.InfinitePlace L => w'.comap (algebraMap K L) = w),
          (w'.mult : ℂ) * ∫ y, Ψ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y))) *
            (Real.log (‖NumberField.AdelicLevel.archEval K w (c : InfiniteAdeleRing K)‖ ^ 2 +
              ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (M y))‖ ^ 2) : ℂ) ∂lam := by sorry
