-- Prove2me | Theorems.Thm_AutomorphicForm_integrable_archIdentGL_inv_mul_diagUnits2_mul_unipotentGL2_sigmaTensor_sub_mul_sigmaGL_mul_of_isArchTestFactor_of_isRegularSemisimple
-- name    : AutomorphicForm.integrable_archIdentGL_inv_mul_diagUnits2_mul_unipotentGL2_sigmaTensor_sub_mul_sigmaGL_mul_of_isArchTestFactor_of_isRegularSemisimple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/514118a5-5de1-5485-b43b-2bf6d88b1f4f
-- title:
--   Integrability of the twisted archimedean descent integrand
-- statement:
--   Let $K \subset L$ be number fields with $L/K$ finite Galois, let $\sigma$ be a $K$-automorphism of $L$ such that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$, and assume $[L:K]$ is prime. Write $E = L \otimes_K \mathbb{A}_{K,\infty}$ for the tensor product of $L$ with the infinite adele ring of $K$, equipped with a measurable structure which is the Borel structure, and let $\mathrm{lam}$ be an additive Haar measure on $E$; similarly $E^{\times}$ carries its Borel structure, and $\theta$ is a Haar measure on the kernel $U_1$ of the map induced on units by the algebra norm $E \to \mathbb{A}_{K,\infty}$. Let $\kappa$ be a Haar measure, for the Borel $\sigma$-algebra, on the subgroup $\mathcal{K}$ of $\mathrm{GL}_2(E)$ cut out as the infimum over the infinite places $w$ of $L$ of the preimages of the row-isometry subgroups of $\mathrm{GL}_2(L_w)$ under $\mathrm{archIdentGL}$ followed by the $w$-component map. Let $\varphi_a : \mathrm{GL}_2(\mathbb{A}_{L,\infty}) \to \mathbb{C}$ be an archimedean test factor, i.e. $\varphi_a(g) = \Phi(\mathrm{archEntries}\, g)$ for some $\mathbb{R}$-smooth $\Phi$ on matrices over the mixed space of $L$, with $\varphi_a$ of compact support, and let $\omega : E \to \mathbb{R}$ be continuous. Let $a, t$ be units of $\mathbb{A}_{K,\infty}$ such that $\mathrm{diag}(a, at)$ is regular semisimple in the sense that $\mathrm{tr}^2 - 4\det$ is a unit, and let $\alpha, \beta \in E^{\times}$ be such that the norm string $\prod_{i<[L:K]} \sigma^i(\mathrm{diag}(\alpha,\beta))$, with $\sigma$ acting entrywise through $\sigma \otimes \mathrm{id}$, equals the image of $\mathrm{diag}(a, at)$ in $\mathrm{GL}_2(E)$ under base change along $A \to L \otimes_K A$. Then the function on $(U_1 \times U_1) \times (E \times \mathcal{K})$ sending $((u_1,u_2),(y,k))$ to $$\varphi_a\Big(\mathrm{archIdentGL}\big(k^{-1} \cdot \mathrm{diag}(\alpha u_1, \beta u_2) \cdot n\big((\sigma \otimes \mathrm{id})(y) - (\alpha u_1)^{-1}(\beta u_2)\, y\big) \cdot \sigma(k)\big)\Big) \cdot \omega(y),$$ where $n(x)$ is the upper unipotent matrix with entry $x$ and $\sigma(k)$ denotes the entrywise action of $\sigma \otimes \mathrm{id}$ on $k$, is integrable for the product measure $(\theta \otimes \theta) \otimes (\mathrm{lam} \otimes \kappa)$.
--
--   This is the integrability hypothesis needed to apply Fubini to the archimedean twisted orbital integral in cyclic base change, after the integral over $\mathrm{GL}_2$ has been descended to the coordinates (norm-one torus)$^2$ × unipotent variable × maximal compact. It feeds the factorisation of twisted orbital integrals at a regular split norm class, and its finiteness rests on the compact support of the test factor together with the invertibility of the twisted difference operator $(\sigma \otimes \mathrm{id}) - r$ guaranteed by the regularity assumption.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrable_archIdentGL_inv_mul_diagUnits2_mul_unipotentGL2_sigmaTensor_sub_mul_sigmaGL_mul_of_isArchTestFactor_of_isRegularSemisimple.lean

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

theorem AutomorphicForm.integrable_archIdentGL_inv_mul_diagUnits2_mul_unipotentGL2_sigmaTensor_sub_mul_sigmaGL_mul_of_isArchTestFactor_of_isRegularSemisimple
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (θ : Measure ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) :
        (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker)
    [θ.IsHaarMeasure]
    (κ : @Measure (↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) (borel _))
    (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (ω : L ⊗[K] InfiniteAdeleRing K → ℝ) (hω : Continuous ω)
    (a t : (InfiniteAdeleRing K)ˣ) (hreg : AutomorphicForm.IsRegularSemisimple (diagUnits2 a (a * t)))
    (α β : (L ⊗[K] InfiniteAdeleRing K)ˣ)
    (hδ : AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (diagUnits2 α β) =
      AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (diagUnits2 a (a * t))) :
    letI : MeasurableSpace ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := borel _
    Integrable
      (fun p : (↥(Units.map (Algebra.norm (InfiniteAdeleRing K) :
            (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker ×
          ↥(Units.map (Algebra.norm (InfiniteAdeleRing K) :
            (L ⊗[K] InfiniteAdeleRing K) →* InfiniteAdeleRing K)).ker) ×
          ((L ⊗[K] InfiniteAdeleRing K) × ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) =>
        φa (AutomorphicForm.archIdentGL K L
          ((p.2.2 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ *
            (diagUnits2 (α * (p.1.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) (β * (p.1.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) *
              AutomorphicForm.unipotentGL2
                (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ p.2.1 -
                  (((α * (p.1.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ))⁻¹ * (β * (p.1.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ)) :
                    (L ⊗[K] InfiniteAdeleRing K)ˣ) : L ⊗[K] InfiniteAdeleRing K) * p.2.1)) *
            AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (p.2.2 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) *
          ((ω p.2.1 : ℝ) : ℂ))
      ((θ.prod θ).prod (lam.prod κ)) := by sorry
