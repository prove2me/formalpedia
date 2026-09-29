-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_twistedCentralizer_tensorArch_integral_eq_integral_prod_toTensorGL_diagUnits2
-- name    : AutomorphicForm.exists_isHaarMeasure_twistedCentralizer_tensorArch_integral_eq_integral_prod_toTensorGL_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/14c56ec9-56b5-5c58-bd5e-f4c8793e16fd
-- title:
--   Haar measure on an archimedean twisted centraliser via K_∞^×× K_∞^×
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ a finite Galois extension, and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $K$-automorphism of $L$ lies in the subgroup of integer powers of $\sigma$ (so $L/K$ is cyclic with generator $\sigma$); let $\nu_A$ be a Haar measure on the unit group $(\mathbb{A}_{K,\infty})^\times$ of the infinite adele ring of $K$, taken with a Borel measurable structure. The assertion is: for every $t \in \mathrm{GL}_2(L)$ whose entries in positions $(1,0)$ and $(0,1)$ vanish and whose ratio of diagonal entries satisfies $N_{L/K}(t_{00}/t_{11}) \neq 1$, and for every $\delta \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_K)$ whose entrywise image under the ring isomorphism $L \otimes_K \mathbb{A}_K \cong \mathbb{A}_L$ equals the entrywise image of $t$ under $L \hookrightarrow \mathbb{A}_L$, there is a measure $\tau_a$ on the $\sigma$-twisted centraliser of $\delta_\infty :=$ the entrywise image of $\delta$ under $\mathrm{id}_L \otimes (\mathbb{A}_K \to \mathbb{A}_{K,\infty})$, that is, on the subgroup of those $s \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$ with $s\,\delta_\infty\,(\sigma s)^{-1} = \delta_\infty$, where $\sigma$ acts entrywise through $\sigma \otimes \mathrm{id}$, carrying its Borel $\sigma$-algebra, such that $\tau_a$ is a Haar measure and, for every function $g : \mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty}) \to \mathbb{C}$ whatsoever, with no measurability or integrability hypothesis, $\int g(s)\,d\tau_a(s)$ over that twisted centraliser equals $\int g\bigl(\mathrm{diag}(1 \otimes a, 1 \otimes b)\bigr)\, d(\nu_A \otimes \nu_A)(a,b)$ over $(\mathbb{A}_{K,\infty})^\times \times (\mathbb{A}_{K,\infty})^\times$.
--
--   This is the archimedean instance of the identification of the $\sigma$-twisted centraliser of a regular diagonal base-change element with a split torus, normalised so that its Haar measure is the image of a product Haar measure on two copies of $K_\infty^\times$; such normalisations are what make twisted orbital integrals on $\mathrm{GL}_2$ comparable with ordinary ones. It is used in the bound [`AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure`](thm.html#AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure) for orbital integrals over double cosets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isHaarMeasure_twistedCentralizer_tensorArch_integral_eq_integral_prod_toTensorGL_diagUnits2.lean

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

theorem AutomorphicForm.exists_isHaarMeasure_twistedCentralizer_tensorArch_integral_eq_integral_prod_toTensorGL_diagUnits2
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [MeasurableSpace (InfiniteAdeleRing K)ˣ] [BorelSpace (InfiniteAdeleRing K)ˣ] (νA : Measure (InfiniteAdeleRing K)ˣ)
    [νA.IsHaarMeasure] :
    ∀ (t : GL (Fin 2) L), (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 → (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 →
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1 →
    ∀ (δ : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)),
      AutomorphicForm.baseChangeGL K L δ = AutomorphicForm.globalPoints (𝓞 L) L t →
    ∃ (τa : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ))
        (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ))),
      @Measure.IsHaarMeasure _ _ _
        (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L δ)) τa ∧
      (∀ g : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ,
        ∫ s : AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L δ),
            g (s : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) ∂τa =
          ∫ p : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ,
            g (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 p.1 p.2)) ∂(νA.prod νA)) := by sorry
