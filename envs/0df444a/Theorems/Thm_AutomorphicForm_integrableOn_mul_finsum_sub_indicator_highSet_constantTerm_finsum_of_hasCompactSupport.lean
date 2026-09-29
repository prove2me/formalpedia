-- Prove2me | Theorems.Thm_AutomorphicForm_integrableOn_mul_finsum_sub_indicator_highSet_constantTerm_finsum_of_hasCompactSupport
-- name    : AutomorphicForm.integrableOn_mul_finsum_sub_indicator_highSet_constantTerm_finsum_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/aa4b5538-6434-5b0b-ba13-cd3cb9fcfd7e
-- title:
--   Integrability of the central fold of a truncated twisted kernel
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, and let $\Phi_L$ be a set of matrices in $\mathrm{GL}_2(\mathbb{A}_L)$. Fix a Haar measure $\nu_{ZL}$ on the idele group $\mathbb{A}_L^\times$ (with its Borel structure) and a set $\Omega_L \subseteq \mathbb{A}_L^\times$ which is a fundamental domain, with respect to $\nu_{ZL}$, for the action of the image of $L^\times$ under the map induced by $L \to \mathbb{A}_L$. Let $D$ be an idelic Galois descent datum for $\mathcal{O}_L, K, L$, that is, a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ which is continuous in each element and compatible with the structure map $L \to \mathbb{A}_L$, let $\sigma \in \mathrm{Gal}(L/K)$, and write $\sigma_D$ for the induced automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$ obtained by applying $D(\sigma)$ entrywise. Let $\xi_L$ be a homomorphism from the full subgroup $\top \le \mathbb{A}_L^\times$ to $\mathbb{C}^\times$ whose associated complex-valued function on $\mathbb{A}_L^\times$ is continuous and which is trivial on the principal ideles. Let $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ be continuous with compact support, let $I, J$ be arbitrary subsets of $\mathrm{GL}_2(L)$, let $R \in \mathbb{R}$ and let $x \in \mathrm{GL}_2(\mathbb{A}_L)$. Then the function
--   $$z \longmapsto \xi_L(z)\Bigl( {\textstyle\sum^{\mathrm{f}}_{\delta \in I}}\, \varphi\bigl(x^{-1}\,\delta\,\sigma_D(c(z)x)\bigr) \;-\; \mathbf{1}_{\{g\,:\,e^{R} < H_L(g)\}}(c(z)x)\cdot \mathrm{CT}\bigl(y \mapsto {\textstyle\sum^{\mathrm{f}}_{\delta \in J}}\,\varphi(x^{-1}\,\delta\,\sigma_D(y))\bigr)(c(z)x)\Bigr)$$
--   is integrable on $\Omega_L$ with respect to $\nu_{ZL}$. Here $\delta$ is viewed in $\mathrm{GL}_2(\mathbb{A}_L)$ through the entrywise map $L \to \mathbb{A}_L$, $c(z)$ is the central scalar matrix $\mathrm{diag}(z,z)$, the sums $\sum^{\mathrm{f}}$ are finsums over the index sets, $H_L$ is the adelic height $\mathrm{adelicHeight}$ of $L$ (the product of the archimedean and finite heights), and $\mathrm{CT}(f)(g)$ is the constant term of $f$ along the unipotent family $t \mapsto \begin{pmatrix} 1 & t \\ 0 & 1\end{pmatrix}$, namely the integral over $\mathbb{A}_L$ of [`AutomorphicForm.constantTermIntegrand`](def/AutomorphicForm_ConstantTerm.html#L44) for this family, $f$ and $g$, taken against the measure carried by `productionPinsOf` for the data $\Phi_L$, the levels $M \mapsto \mathrm{levelOne}(M) \sqcap \mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators and the box $\mathrm{adelicBox}(L)$; that measure is the adelic additive Haar measure conditioned on $\mathrm{adelicBox}(L)$, and the Borel structure on $\mathbb{A}_L$ is the one recorded by the same datum.
--
--   This is the pointwise-in-$x$ integrability, uniform in the index sets $I$ and $J$, of the central fold of the truncated hyperbolic-type kernel occurring in the twisted (base-change) trace formula for $\mathrm{GL}_2$. It is the integrability conjunct consumed by the hyperbolic-term results, in particular by [`AutomorphicForm.exists_forall_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_orbital_add_sum_weightedOrbital_or_eq_zero_of_isFactorizableTestFn`](thm.html#AutomorphicForm.exists_forall_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_orbital_add_sum_weightedOrbital_or_eq_zero_of_isFactorizableTestFn), where the freedom in $I$ and $J$ permits the class-by-class splitting of the hyperbolic contribution to be interchanged with the idelic integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrableOn_mul_finsum_sub_indicator_highSet_constantTerm_finsum_of_hasCompactSupport.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.integrableOn_mul_finsum_sub_indicator_highSet_constantTerm_finsum_of_hasCompactSupport
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (I J : Set (GL (Fin 2) L)) (R : ℝ) (x : AdelicGL2 (𝓞 L) L) :
    IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∑ᶠ δ ∈ I,
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ J,
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL := by sorry
