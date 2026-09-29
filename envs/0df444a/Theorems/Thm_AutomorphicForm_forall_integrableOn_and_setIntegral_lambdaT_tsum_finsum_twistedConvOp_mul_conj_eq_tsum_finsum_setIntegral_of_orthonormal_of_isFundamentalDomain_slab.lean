-- Prove2me | Theorems.Thm_AutomorphicForm_forall_integrableOn_and_setIntegral_lambdaT_tsum_finsum_twistedConvOp_mul_conj_eq_tsum_finsum_setIntegral_of_orthonormal_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.forall_integrableOn_and_setIntegral_lambdaT_tsum_finsum_twistedConvOp_mul_conj_eq_tsum_finsum_setIntegral_of_orthonormal_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/d242769f-6c8e-5206-840d-1d1f9467722f
-- title:
--   Truncated twisted cuspidal kernel integrates blockwise over a fundamental domain
-- statement:
--   Let $L/K$ be an extension of number fields, let $D$ be an idele Galois descent datum for $L/K$ (a continuous action of $L\simeq_K L$ on the adele ring $\mathbb{A}_L$ compatible with $L\to\mathbb{A}_L$), and let $\sigma$ be a $K$-automorphism of $L$. Fix reals $0<\alpha<\beta$ and write $\mathcal S=\{g : \|\det g\|\in[\alpha,\beta]\}$ for the slab in $G=\mathrm{GL}_2(\mathbb{A}_L)$ cut out by the idele norm `ideleNorm` of the determinant. Let $\Phi_L$ and $\Phi_0$ be subsets of $\mathcal S$, each a fundamental domain for the image of $\mathrm{GL}_2(L)$ in $G$ with respect to adelic Haar measure on $G$ restricted to $\mathcal S$. Let $\xi_L$ be a character of the full group of ideles of $L$, let $S_L$ be a finite set of finite places of $L$ which is a union of fibres over $K$, let $N$ be an ideal of $\mathcal O_L$ all of whose prime divisors lie in $S_L$, and let `tysL` be a family of archimedean types. All spectral data are taken for the carrier `productionPinsOf L ΦL` with level subgroups $U(M)=\mathrm{levelOne}(M)\cap\mathrm{GL}_2(\mathbb{A}_{L,\mathrm{fin}})$, Hecke generators `heckeGen`, centre the full idele group, Haar measures on $G$ and the conditional additive adelic measure on the adelic box. Given an index type $\iota$, functions $b_i:G\to\mathbb{C}$ and classes $\mathrm{cls}(i)$ such that each $\mathrm{cls}(i)$ is a cuspidal class (level $N$, Hecke and central eigenvalues vanishing on $S_L$, nonzero isotypic space) and each $b_i$ lies in the isotypic cusp submodule for $\mathrm{cls}(i)$ intersected with the archimedean cut submodule `archCutSubmodule L tysL`; assume $\int_{\Phi_L}b_i\overline{b_i}=1$, $\int_{\Phi_L}b_i\overline{b_j}=0$ for $i\ne j$, and that for each cuspidal class $\pi$ the set $\{i:\mathrm{cls}(i)=\pi\}$ is finite with $\mathbb{C}$-span of the corresponding $b_i$ equal to that cut isotypic space. Let $\varphi:G\to\mathbb{C}$ be continuous with compact support, factorizable (a smooth compactly supported archimedean factor times a locally constant compactly supported finite factor), bi-invariant under $\mathrm{levelOne}(N)\cap\mathrm{GL}_2(\mathbb{A}_{L,\mathrm{fin}})$ and archimedean bi-finite of the types `tysL`, and let $R\in\mathbb{R}$. Consider, for $x\in G$, the value at $y=x$ of the truncation `lambdaT` at threshold $\exp R$ — subtraction of the indicator of $\{\mathrm{adelicHeight}>\exp R\}$ times the constant term along the unipotent family $t\mapsto\mathrm{unipotentGL2}(t)$ against the carrier's adelic measure — applied in the variable $y$ to $$y\mapsto\sum_{\Psi}\ \sum_{i:\,\mathrm{cls}(i)=\Psi}\bigl(\textstyle\int_G b_i(\sigma_{\mathbb A}(xz))\varphi(z)\,dz\bigr)\overline{b_i(y)},$$ the outer sum running over cuspidal classes $\Psi$. The theorem asserts that this function of $x$ is integrable on $\Phi_0$ for adelic Haar measure, and that its integral over $\Phi_0$ equals $\sum_{\Psi}\sum_{i:\,\mathrm{cls}(i)=\Psi}\int_{\Phi_0}\bigl(\int_G b_i(\sigma_{\mathbb A}(xz))\varphi(z)\,dz\bigr)\overline{b_i(x)}\,dx$.
--
--   This is the cuspidal block of the spectral side of the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over $L/K$: the truncation operator has no effect on the twisted cuspidal kernel, and the expansion of the kernel along an adapted orthonormal system may be integrated over a fundamental domain term by term. It feeds the comparison of the truncated twisted kernel with its untwisted form and the limit computation that isolates the twisted trace.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_integrableOn_and_setIntegral_lambdaT_tsum_finsum_twistedConvOp_mul_conj_eq_tsum_finsum_setIntegral_of_orthonormal_of_isFundamentalDomain_slab.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.forall_integrableOn_and_setIntegral_lambdaT_tsum_finsum_twistedConvOp_mul_conj_eq_tsum_finsum_setIntegral_of_orthonormal_of_isFundamentalDomain_slab
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
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
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL ∧
      b i ∈ isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL (cls i) ⊓ archCutSubmodule L tysL)
    (hb₁ : ∀ i, ∫ g in ΦL, b i g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 1)
    (hb₀ : ∀ i j, i ≠ j → ∫ g in ΦL, b i g * conj (b j g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 0)
    (hbs : ∀ π ∈ cuspClasses L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL,
      {i | cls i = π}.Finite ∧
      Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL π ⊓ archCutSubmodule L tysL)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφf : IsFactorizableTestFn L φ)
    (hφU : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ)
    (hφt : IsArchBiFinite L tysL φ) (R : ℝ) :
    IntegrableOn (fun x =>
        (@AutomorphicForm.lambdaT _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
          (fun y => ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                Ψ ∈ cuspClasses L
                  (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
              ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
          x))
      Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
    ∫ x in Φ₀,
        (@AutomorphicForm.lambdaT _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
          (fun y => ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                Ψ ∈ cuspClasses L
                  (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
              ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
          x)
      ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
    ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
        Ψ ∈ cuspClasses L
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
      ∑ᶠ i : {i // cls i = Ψ.1},
        ∫ x in Φ₀, twistedConvOp K L D σ φ (b i) x * conj (b i x)
          ∂(adelicGLHaar (Fin 2) (𝓞 L) L) := by sorry
