-- Prove2me | Theorems.Thm_AutomorphicForm_forall_integrableOn_and_setIntegral_lambdaT_tsum_convOp_mul_conj_sigmaAdelicAct_symm_eq_tsum_finsum_setIntegral_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.forall_integrableOn_and_setIntegral_lambdaT_tsum_convOp_mul_conj_sigmaAdelicAct_symm_eq_tsum_finsum_setIntegral_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/9252eb53-9ea5-5d2c-836c-24d957e35818
-- title:
--   Truncated cuspidal kernel integrated along a Galois-twisted diagonal
-- statement:
--   Let $K \subseteq L$ be number fields, $D$ a Galois descent datum for the adeles of $L$ (a continuous action of $\mathrm{Aut}_K(L)$ on $\mathbb{A}_L$ by ring automorphisms extending the action on principal adeles), $\sigma$ a $K$-automorphism of $L$, and write $\sigma_{\mathbb{A}}$ for the induced map `sigmaAdelicAct K L D σ.symm` on $\mathrm{GL}_2(\mathbb{A}_L)$. Fix $0 < \alpha < \beta$ and two sets $\Phi, \Phi_0$ contained in the slab $\{g : \|\det g\| \in [\alpha,\beta]\}$, each a fundamental domain for the image of $\mathrm{GL}_2(L)$ acting on adelic Haar measure $\mu$ restricted to that slab. Fix a character $\xi$ of the full group of idele units, a finite set $S_L$ of finite places of $L$ that is a union of fibres over $K$, an ideal $N$ whose prime divisors all lie in $S_L$, and an archimedean type family $\mathrm{tys}_L$. Let the carrier data be `productionPinsOf L Φ` with level family $M \mapsto \mathrm{principalLevel}(M) \cap \mathrm{GL}_2(\mathbb{A}_L)_{\mathrm{fin}}$, Hecke generators `heckeGen`, central subgroup $\top$, and the conditioned additive Haar measure $\nu$ on the adelic box. Let $\iota$ be a type, $b : \iota \to (\mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C})$ and $\mathrm{cls} : \iota \to$ Hecke eigensystems such that each $\mathrm{cls}(i)$ lies in `cuspClasses` (level $N$, vanishing Hecke and central data on $S_L$, non-zero isotypic space) and each $b_i$ lies in the isotypic cusp submodule of $\mathrm{cls}(i)$ intersected with the archimedean cut submodule; assume $\int_\Phi b_i \overline{b_i}\,d\mu = 1$, $\int_\Phi b_i \overline{b_j}\,d\mu = 0$ for $i \neq j$, and that for every cuspidal class $\pi$ the fibre $\{i : \mathrm{cls}(i) = \pi\}$ is finite with $\mathbb{C}$-span of its $b_i$ equal to that intersected isotypic space. Let $f$ be continuous with compact support, factorizable (a smooth compactly supported archimedean factor times a locally constant compactly supported finite factor), bi-invariant under $\mathrm{principalLevel}(N) \cap \mathrm{GL}_2(\mathbb{A}_L)_{\mathrm{fin}}$, and archimedeanly bi-finite for $\mathrm{tys}_L$; let $R \in \mathbb{R}$. Then the function $x \mapsto \big(\lambda_{e^R}\,[\,y \mapsto \sum_i' (f \ast b_i)(x)\,\overline{b_i(y)}\,]\big)(\sigma_{\mathbb{A}} x)$, where $f \ast b_i =$ `convOp L f (b i)` is the right convolution $g \mapsto \int b_i(gx) f(x)\,d\mu$ and $\lambda_{e^R}$ subtracts, on the locus where the adelic height exceeds $e^R$, the constant term along $t \mapsto \mathrm{unipotentGL2}(t)$ integrated against $\nu$, is integrable on $\Phi_0$ for $\mu$, and its integral over $\Phi_0$ equals the sum over cuspidal classes $\Psi$ of the finite sums over $\{i : \mathrm{cls}(i) = \Psi\}$ of $\int_{\Phi_0} (f \ast b_i)(x)\,\overline{b_i(\sigma_{\mathbb{A}} x)}\,d\mu$.
--
--   This is the cuspidal-kernel step of the Galois-twisted trace formula for $\mathrm{GL}_2$ over $L$: the truncation operator $\lambda_T$ removes nothing from the cuspidal kernel, and the twisted diagonal integral over a fundamental domain decomposes as a sum over cuspidal Hecke eigensystem classes of the contributions of the individual orthonormal cusp forms. It feeds the comparison of the twisted convolution expansion with the $\sigma$-twisted kernel integral used in the base-change argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_integrableOn_and_setIntegral_lambdaT_tsum_convOp_mul_conj_sigmaAdelicAct_symm_eq_tsum_finsum_setIntegral_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.lean

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
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.forall_integrableOn_and_setIntegral_lambdaT_tsum_convOp_mul_conj_sigmaAdelicAct_symm_eq_tsum_finsum_setIntegral_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ι : Type) (b : ι → AdelicGL2 (𝓞 L) L → ℂ) (cls : ι → HeckeEigensystem L ℂ)
    (hb : ∀ i, cls i ∈ cuspClasses L
        (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL ∧
      b i ∈ isotypicCuspSubmodule L
        (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL (cls i) ⊓ archCutSubmodule L tysL)
    (hb₁ : ∀ i, ∫ g in Φ, b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 1)
    (hb₀ : ∀ i j, i ≠ j → ∫ g in Φ, b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0)
    (hbs : ∀ π ∈ cuspClasses L
        (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL,
      {i | cls i = π}.Finite ∧
      Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule L
        (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL π ⊓ archCutSubmodule L tysL)
    (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hff : IsFactorizableTestFn L f)
    (hfU : IsBiInvariantUnder L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) f)
    (hft : IsArchBiFinite L tysL f) (R : ℝ) :
    IntegrableOn (fun x =>
        (@AutomorphicForm.lambdaT _
          (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun v => heckeGen (𝓞 L) L v) (adelicBox L)).nS _ _
          (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun v => heckeGen (𝓞 L) L v) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
          (fun y => ∑' i : ι, convOp L f (b i) x * conj (b i y))
          (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)))
      Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
    ∫ x in Φ₀,
        (@AutomorphicForm.lambdaT _
          (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun v => heckeGen (𝓞 L) L v) (adelicBox L)).nS _ _
          (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun v => heckeGen (𝓞 L) L v) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
          (fun y => ∑' i : ι, convOp L f (b i) x * conj (b i y))
          (AutomorphicForm.sigmaAdelicAct K L D σ.symm x))
      ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
    ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
        Ψ ∈ cuspClasses L
          (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL},
      ∑ᶠ i : {i // cls i = Ψ.1},
        ∫ x in Φ₀, convOp L f (b i) x * conj (b i (AutomorphicForm.sigmaAdelicAct K L D σ.symm x))
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by sorry
