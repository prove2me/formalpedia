-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_exists_isHaarMeasure_twistedCentralizer_integral_eq_mul_integral_prod_toTensorGL_diagUnits2
-- name    : AutomorphicForm.exists_pos_forall_exists_isHaarMeasure_twistedCentralizer_integral_eq_mul_integral_prod_toTensorGL_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/95076810-c7d0-5faa-9e8d-08a73fcc935d
-- title:
--   Twisted centraliser of a regular diagonal base-change element: Haar measure comparison
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite Galois extension of $K$, and let $\sigma$ be a $K$-automorphism of $L$ such that every $K$-automorphism of $L$ is an integer power of $\sigma$ (so $\mathrm{Gal}(L/K)$ is cyclic with generator $\sigma$). Fix a Borel measurable structure on the unit group $(\mathbb{A}_K)^\times$ of the adele ring of $K$ and a Haar measure $\nu_K$ on it. Then there is a real constant $c_\tau>0$, depending on none of the data below, with the following property. Let $t\in\mathrm{GL}_2(L)$ have vanishing $(1,0)$ and $(0,1)$ entries and satisfy $N_{L/K}(t_{00}/t_{11})\neq 1$, and let $\delta\in\mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$ be such that the image of $\delta$ under the map of general linear groups induced by the ring isomorphism $L\otimes_K\mathbb{A}_K\cong\mathbb{A}_L$ equals the image of $t$ under $\mathrm{GL}_2(L)\to\mathrm{GL}_2(\mathbb{A}_L)$. Then on the subgroup $\{s\in\mathrm{GL}_2(L\otimes_K\mathbb{A}_K) : s\,\delta\,(\sigma s)^{-1}=\delta\}$, where $\sigma$ acts through its semilinear extension to $L\otimes_K\mathbb{A}_K$ entrywise, carrying the Borel $\sigma$-algebra of its subspace topology, there exists a Haar measure $\tau$ such that for every function $g:\mathrm{GL}_2(L\otimes_K\mathbb{A}_K)\to\mathbb{C}$,
--   $$\int_{\{s\,\delta\,(\sigma s)^{-1}=\delta\}} g(s)\,d\tau(s)\;=\;c_\tau\int_{(\mathbb{A}_K)^\times\times(\mathbb{A}_K)^\times} g\bigl(1\otimes\mathrm{diag}(a,b)\bigr)\,d(\nu_K\times\nu_K)(a,b),$$
--   the diagonal matrix $\mathrm{diag}(a,b)$ being pushed into $\mathrm{GL}_2(L\otimes_K\mathbb{A}_K)$ along $a\mapsto 1\otimes a$. No measurability or integrability hypothesis is imposed on $g$, the Bochner integral being zero for non-integrable functions.
--
--   This is the computation of the $\sigma$-twisted centraliser of a base-change element attached to a regular diagonal $t\in\mathrm{GL}_2(L)$: it is the diagonal torus of $\mathrm{GL}_2$ over $\mathbb{A}_K$, and its Haar measure is compared, by a single constant valid for all such $t$ and all lifts $\delta$, with the product Haar measure on $(\mathbb{A}_K)^\times\times(\mathbb{A}_K)^\times$. The torus datum $(c_\tau,\tau)$ it produces feeds the twisted orbital integral estimates and the centre-unfolding identities used in the comparison of trace formulae for $\mathrm{GL}_2$ over $L$ and over $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_exists_isHaarMeasure_twistedCentralizer_integral_eq_mul_integral_prod_toTensorGL_diagUnits2.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_pos_forall_exists_isHaarMeasure_twistedCentralizer_integral_eq_mul_integral_prod_toTensorGL_diagUnits2
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ] (νK : Measure (AdeleRing (𝓞 K) K)ˣ)
    [νK.IsHaarMeasure] :
    ∃ cτ : ℝ, 0 < cτ ∧
    ∀ (t : GL (Fin 2) L), (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 →
    ∀ (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)),
      AutomorphicForm.baseChangeGL K L δ = AutomorphicForm.globalPoints (𝓞 L) L t →
    ∃ (τ : @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ)),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ δ) τ ∧
      (∀ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ,
        ∫ s : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ δ,
            g (s : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∂τ =
          cτ * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
            g (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2)) ∂(νK.prod νK)) := by sorry
