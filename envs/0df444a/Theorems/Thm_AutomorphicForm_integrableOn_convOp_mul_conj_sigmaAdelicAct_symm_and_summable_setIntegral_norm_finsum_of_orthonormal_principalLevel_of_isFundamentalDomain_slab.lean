-- Prove2me | Theorems.Thm_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/8f8e262c-32f3-5676-b691-ab6f549e9499
-- title:
--   Trace-class convolution on the cut cuspidal spectrum, Galois-twisted
-- statement:
--   Let $K \subseteq L$ be number fields, let $D$ be an idelic Galois descent datum for $L/K$, i.e. a monoid homomorphism $\sigma \mapsto D.\mathrm{act}\,\sigma$ from $\mathrm{Aut}_K(L)$ to ring automorphisms of $\mathbb{A}_L$ that are continuous and compatible with $L \to \mathbb{A}_L$, and let $\sigma \in \mathrm{Aut}_K(L)$. Let $0 < \alpha < \beta$ and let $\Phi, \Phi_0$ be two subsets of the slab $\{g : \|\det g\| \in [\alpha,\beta]\}$ (the norm being the modulus character of $\mathbb{A}_L^\times$), each a fundamental domain for the image of $\mathrm{GL}_2(L)$ in $\mathrm{GL}_2(\mathbb{A}_L)$ with respect to the Haar measure `adelicGLHaar` restricted to that slab. Let $\xi$ be a homomorphism from the full idele unit group to $\mathbb{C}^\times$, let $S_L$ be a finite set of finite places of $L$ whose membership depends only on the place of $K$ below, let $N$ be an ideal of $\mathcal{O}_L$ all of whose prime divisors lie in $S_L$, and let $\mathrm{tys}_L$ be a family assigning to each infinite place $w$ of $L$ finitely many representations of the relevant row-isometry group. Write $\mathrm{pins}$ for the carrier data built from $\Phi$, the level family $M \mapsto U(M) \sqcap \mathrm{GL}_2(\mathbb{A}_L)^{\mathrm{fin}}$ (principal level met with the kernel of the archimedean projection), the Hecke generators `heckeGen`, the adelic box, the full central subgroup and the Haar measures. Let $\iota$ be a type, $b : \iota \to (\mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C})$ and $\mathrm{cls} : \iota \to$ Hecke eigensystems over $\mathbb{C}$, such that for each $i$: $\mathrm{cls}\,i$ is a cuspidal class (level $N$, vanishing $a_v, b_v$ at $v \in S_L$, nonzero isotypic space) and $b_i$ lies in the span of the isotypic cusp forms for $\mathrm{cls}\,i$ intersected with the archimedean cut submodule for $\mathrm{tys}_L$; moreover $\int_\Phi b_i \overline{b_i} = 1$, $\int_\Phi b_i \overline{b_j} = 0$ for $i \neq j$, and for every cuspidal class $\pi$ the fibre $\{i : \mathrm{cls}\,i = \pi\}$ is finite and the $b_i$ over it span that cut isotypic space. Finally let $f$ be continuous with compact support, factorizable as a smooth compactly supported archimedean factor times a locally constant compactly supported finite factor, bi-invariant under $U(N) \sqcap \mathrm{GL}_2(\mathbb{A}_L)^{\mathrm{fin}}$, and archimedean-bi-finite for $\mathrm{tys}_L$ in the sense that $g \mapsto f(g^{-1})$ lies in the archimedean cut submodule and $f$ in the dual cut submodule. Then, with $R(f)b_i = \big(x \mapsto \int b_i(xy) f(y)\,d\mu(y)\big)$ and $\sigma_{\mathbb{A}}^{-1}$ the entrywise action of $D.\mathrm{act}\,\sigma^{-1}$ on $\mathrm{GL}_2(\mathbb{A}_L)$: for every $i$ the function $x \mapsto (R(f)b_i)(x)\,\overline{b_i(\sigma_{\mathbb{A}}^{-1}x)}$ is integrable on $\Phi_0$, and the function sending a Hecke eigensystem $\Psi$ to $\int_{\Phi_0} \big\| \sum_{i : \mathrm{cls}\,i = \Psi} (R(f)b_i)(x)\,\overline{b_i(\sigma_{\mathbb{A}}^{-1}x)} \big\|\,d\mu(x)$ is summable over all Hecke eigensystems.
--
--   This is the absolute-convergence (trace-class) input for the cuspidal side of the twisted trace formula on $\mathrm{GL}_2$: the kernel of $R(f)$ restricted to the cut cuspidal spectrum, paired against the $\sigma$-twisted diagonal and read over a second fundamental domain, converges class by class and the classes may be summed. It is used in the subsequent computation of the $\sigma$-twisted spectral integral as a sum over Hecke eigensystems of class-by-class contributions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.lean

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

theorem AutomorphicForm.integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
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
    (hft : IsArchBiFinite L tysL f) :
    (∀ i, IntegrableOn
        (fun x => convOp L f (b i) x * conj (b i (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L)) ∧
    Summable (fun Ψ : HeckeEigensystem L ℂ =>
      ∫ x in Φ₀, ‖∑ᶠ i : {i // cls i = Ψ},
          convOp L f (b i) x * conj (b i (AutomorphicForm.sigmaAdelicAct K L D σ.symm x))‖
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) := by sorry
