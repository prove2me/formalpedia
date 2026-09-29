-- Prove2me | Theorems.Thm_AutomorphicForm_integrableOn_and_setIntegral_lambdaT_tsum_finsum_twistedConvOp_mul_conj_eq_setIntegral_lambdaT_tsum_convOp_mul_conj_sigmaAdelicAct_symm
-- name    : AutomorphicForm.integrableOn_and_setIntegral_lambdaT_tsum_finsum_twistedConvOp_mul_conj_eq_setIntegral_lambdaT_tsum_convOp_mul_conj_sigmaAdelicAct_symm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/f2a924d8-641b-5039-be3a-06aed5448706
-- title:
--   Twisted and untwisted truncated cuspidal kernels integrate equally
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ an algebra over $K$, and $\mathrm{GL}_2(\mathbb{A}_L)$ denotes `AdelicGL2 (𝓞 L) L`, equipped with its Borel structure and the Haar measure `adelicGLHaar (Fin 2) (𝓞 L) L`; [`NumberField.TateGlobal.ideleNorm L`](def/NumberField_TateGlobalZeta.html#L19) is the idele norm $z \mapsto \|z\|$ given by the distributive Haar character of $\mathbb{A}_L$, and the *slab* is the set $\{g : \|\det g\| \in [\alpha,\beta]\}$.
--
--   **Slab and fundamental domains.** Real numbers $\alpha,\beta$ with $0 < \alpha$ and $\alpha < \beta$ are given. The set $\Phi_L \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ is contained in the slab (`hΦs`) and is a fundamental domain for the image of $\mathrm{GL}_2(L)$ under `globalPoints (𝓞 L) L` acting on $\mathrm{GL}_2(\mathbb{A}_L)$, for the Haar measure restricted to the slab (`hΦ`). A second set $\Phi_0$ is given together with: real parameters $c,u,d_1,d_2$ with $0 < c$, a compact set $T_c$, and the requirement `hΦ₀S` that $\Phi_0$ be covered by the right translates $(\cdot\, y)''\,$ of the centre-cut Siegel set `WindowedSiegel.centreCutSiegelSet L c u d₁ d₂` as $y$ ranges over $T_c$; further $\Phi_0$ lies in the slab (`hΦ₀s`) and is itself a fundamental domain for $\mathrm{GL}_2(L)$ with respect to the slab-restricted Haar measure (`hΦ₀`).
--
--   **Central data.** The idele group $\mathbb{A}_L^{\times}$ carries a measurable structure which is Borel, a Haar measure $\nu_{Z_L}$, and a set $\Omega_L$ which is a fundamental domain for the image of $L^{\times}$ in $\mathbb{A}_L^{\times}$ with respect to $\nu_{Z_L}$ (`hΩL`).
--
--   **Descent and Galois data.** $D$ is an [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), that is, a homomorphism from $\mathrm{Aut}_K(L)$ to the ring automorphisms of $\mathbb{A}_L$ which is compatible with $L \to \mathbb{A}_L$ and continuous in each automorphism; $\sigma : L \simeq_{\mathrm{alg}[K]} L$ is a $K$-automorphism. [`AutomorphicForm.sigmaAdelicAct K L D σ.symm`](def/AutomorphicForm_SigmaAdelicAction.html#L14) is the induced monoid endomorphism of $\mathrm{GL}_2(\mathbb{A}_L)$ obtained by applying $D.\mathrm{act}\,\sigma^{-1}$ entrywise, and `D.unitsAct σ` the induced automorphism of $\mathbb{A}_L^{\times}$.
--
--   **Character, level and type data.** $S_L$ is a finite set of height-one primes of $\mathcal{O}_L$ which is a union of fibres over $\mathcal{O}_K$, in the sense that $w \in S_L \iff w' \in S_L$ whenever $w$ and $w'$ lie under the same prime of $\mathcal{O}_K$ (`hSL`). The homomorphism $\xi_L$ from the full subgroup $\top \le \mathbb{A}_L^{\times}$ to $\mathbb{C}^{\times}$ is continuous as a $\mathbb{C}$-valued function (`hξc`), trivial on the image of $L^{\times}$ (`hξt`), and of absolute value $|\xi_L(z)| = \|z\|^{w}$ for a real exponent $w$ (`hξw`). The ideal $N$ of $\mathcal{O}_L$ is such that every prime dividing $N$ lies in $S_L$ (`hN`). The family $\mathrm{tys}_L$ is an `ArchTypeFamily L`, assigning to each infinite place a finite list of representations of the row-isometry subgroup; `archCutSubmodule L tysL` is the intersection over the infinite places of the sums of the corresponding type subspaces. Two further characters are given: $\xi'$ with $\xi'(z) = \xi_L(D.\mathrm{unitsAct}\,\sigma\, z)$ (`hξ'`), i.e. $\xi'$ is $\xi_L$ transported by $\sigma$, and $\xi_0$ with $\xi_0(z)\cdot \|z\|^{w} = \xi'(z)$ for all ideles $z$ (`hξ₀`), i.e. $\xi_0$ is the unitary part of $\xi'$.
--
--   Write $P_1$ for the carrier pins `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)`: the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_L)$, the domain $\Phi_L$, central subgroup $\top$, the open subgroups $\mathrm{levelOne}(M)$ intersected with the kernel of the archimedean projection, the Hecke generators at the finite places, and, on $\mathbb{A}_L$, the Borel structure together with the additive Haar measure conditioned to the adelic box `adelicBox L`. Write $P_2$ for the analogous pins built from the canonical truncation domain [`AutomorphicForm.canonicalTruncationDomain L α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) and the subgroups $\mathrm{principalLevel}(M) \sqcap \mathrm{finiteAdelicGL2Subgroup}$.
--
--   **Orthonormal system at level-one pins.** A type $\iota$, functions $b_i : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ and eigensystems $\mathrm{cls}(i) \in$ `HeckeEigensystem L ℂ` are given with: each $\mathrm{cls}(i)$ in `cuspClasses L P₁ ξL N SL` (level $N$, vanishing Hecke and central data on $S_L$, non-zero isotypic space) and $b_i$ in the intersection of `isotypicCuspSubmodule L P₁ ξL N SL (cls i)` with `archCutSubmodule L tysL` (`hb`); normalisation $\int_{\Phi_L} b_i \overline{b_i} = 1$ (`hb₁`) and orthogonality $\int_{\Phi_L} b_i \overline{b_j} = 0$ for $i \neq j$ (`hb₀`); for each class $\pi$ the fibre $\{i : \mathrm{cls}(i) = \pi\}$ is finite and the $\mathbb{C}$-span of the corresponding $b_i$ is exactly the cut isotypic space at $\pi$ (`hbs`); and completeness (`hbc`): any $\psi$ which is a smooth cuspidal automorphic function at $P_1$ for $\xi_L$, continuous, right invariant under $P_1.U\,N$, lying in the archimedean cut subspace, and orthogonal to every $b_i$ over $\Phi_L$, vanishes almost everywhere on $\Phi_L$.
--
--   **Orthonormal system at principal-level pins.** Correspondingly, a type $\iota'$, functions $b'_i$ and eigensystems $\mathrm{cls}'(i)$ are given for the pins $P_2$ and the character $\xi_0$, with the same four requirements, all integrals being taken over [`AutomorphicForm.canonicalTruncationDomain L α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32): membership in the cusp classes and in the cut isotypic spaces (`hb'`), normalisation (`hb'n`), orthogonality (`hb'o`), finiteness of the fibres and spanning of the cut isotypic spaces (`hb's`), and completeness against the cut cuspidal space (`hb'c`).
--
--   **Test function.** $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ is continuous (`hφ`), of compact support (`hφc`), factorizable in the sense of `IsFactorizableTestFn L` (a smooth compactly supported archimedean factor times a locally constant compactly supported finite factor) (`hfact`), bi-invariant under $\mathrm{levelOne}(N) \sqcap \mathrm{finiteAdelicGL2Subgroup}\,L$ (`hbi`), and archimedeanly bi-finite for $\mathrm{tys}_L$ (`harch`). The function $\varphi'$ is its shift $\varphi'(g) = \varphi(g)\cdot \|\det g\|^{w/2}$ (`hφ'`).
--
--   **Conclusion.** Put $V = (\nu_{Z_L}(\Omega_L \cap \{z : \|\det(z \cdot I_2)\| \in [\alpha,\beta]\}))$, read as a real number and then as a complex number, where $z \cdot I_2$ is `centralScalar (𝓞 L) L z`. For every real $R$, with truncation parameter $T = \exp R$ performed by [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48) with respect to the measurable structure $P_1.\mathrm{nS}$ and the measure $P_1.\nu$ on $\mathbb{A}_L$, the unipotent family $t \mapsto$ [`AutomorphicForm.unipotentGL2 t`](def/AutomorphicForm_ConstantTerm.html#L17), and the height [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158) — so that $\lambda_T\psi(g) = \psi(g) - \mathbf{1}_{\{\mathrm{adelicHeight}(g) > T\}}(g)\cdot \mathrm{constantTerm}(\psi)(g)$ — the following three assertions hold, the truncation being applied each time in the second kernel variable $y$ with the first variable $x$ held fixed:
--
--   1.
--
--   the function
--   $$x \mapsto \lambda_T\Big(y \mapsto V\cdot \sum_{\Psi}{}' \ \sum^{\mathrm{f}}_{\,i \,:\, \mathrm{cls}(i) = \Psi} (\mathrm{twistedConvOp}\,K\,L\,D\,\sigma\,\varphi\,(b_i))(x)\cdot \overline{b_i(y)}\Big)(x)$$
--   is integrable on $\Phi_0$ for `adelicGLHaar (Fin 2) (𝓞 L) L`; here the outer sum is the unconditional sum over the subtype of $\Psi$ in `cuspClasses L P₁ ξL N SL`, the inner one the finite sum over the subtype $\{i : \mathrm{cls}(i) = \Psi\}$, and `twistedConvOp K L D σ φ (b i)` is $x \mapsto \int b_i(\sigma_{\mathbb{A}}(x\,g))\,\varphi(g)\,dg$, the right convolution of $\varphi$ against $b_i \circ$ `sigmaAdelicAct K L D σ`;
--
--   2.
--
--   the function
--   $$x \mapsto \lambda_T\Big(y \mapsto V\cdot \sum_{i : \iota'}{}' (\mathrm{convOp}\,L\,\varphi'\,(b'_i))(x)\cdot \overline{b'_i(y)}\Big)\big(\mathrm{sigmaAdelicAct}\,K\,L\,D\,\sigma^{-1}\,x\big)$$
--   is integrable on $\Phi_0$ for the same measure; here `convOp L φ' (b' i)` is $x \mapsto \int b'_i(x\,g)\,\varphi'(g)\,dg$, and the truncated kernel is evaluated at the image of $x$ under the entrywise action of $D.\mathrm{act}\,\sigma^{-1}$;
--
--   3.
--
--   the integrals over $\Phi_0$ of the two functions in 1 and 2, with respect to `adelicGLHaar (Fin 2) (𝓞 L) L`, are equal.
--
--   Both truncations use the same data attached to $P_1$, namely the Borel structure on $\mathbb{A}_L$ and the Haar measure conditioned to the adelic box, and the same height and threshold $\exp R$.
--
--   This is the comparison of the cuspidal contributions on the two sides of the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over $L/K$: the truncated twisted cuspidal kernel attached to $(\xi_L, N, S_L)$ at level-one pins, integrated over a fundamental domain inside the slab $\|\det\| \in [\alpha,\beta]$, agrees with the truncated untwisted cuspidal kernel of the unitary character $\xi_0$ at principal-level pins read along the twisted diagonal $x \mapsto (x,\sigma^{-1}x)$, both integrals existing. It feeds the $\sigma$-twisted continuous-term package of the twisted trace formula on the route to base change for $\mathrm{GL}_2$, being used by [`AutomorphicForm.exists_forall_setIntegral_lambdaT_sigmaAdelicAct_sub_twistedConvOp_sub_chiDet_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_sigmaAdelicAct`](thm.html#AutomorphicForm.exists_forall_setIntegral_lambdaT_sigmaAdelicAct_sub_twistedConvOp_sub_chiDet_eq_mul_tsum_integral_sum_rightConv_mul_setIntegral_lambdaT_mul_conj_lambdaT_sigmaAdelicAct).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrableOn_and_setIntegral_lambdaT_tsum_finsum_twistedConvOp_mul_conj_eq_setIntegral_lambdaT_tsum_convOp_mul_conj_sigmaAdelicAct_symm.lean

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

theorem AutomorphicForm.integrableOn_and_setIntegral_lambdaT_tsum_finsum_twistedConvOp_mul_conj_eq_setIntegral_lambdaT_tsum_convOp_mul_conj_sigmaAdelicAct_symm
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ))
    (ξ' : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξ' : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξ' ⟨z, Subgroup.mem_top z⟩ = ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩)
    (ξ₀ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξ₀ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ((ξ₀ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      (((NumberField.TateGlobal.ideleNorm L z) ^ (w) : ℝ) : ℂ) = ((ξ' ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
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
    (hbc : ∀ ψ : AdelicGL2 (𝓞 L) L → ℂ,
      IsSmoothCuspAutomorphicFnAt L
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL ψ →
      Continuous ψ →
      (∀ g : AdelicGL2 (𝓞 L) L, ∀ k ∈
        (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).U N, ψ (g * k) = ψ g) →
      ψ ∈ archCutSubmodule L tysL →
      (∀ i, ∫ g in ΦL, ψ g * conj (b i g) ∂adelicGLHaar (Fin 2) (𝓞 L) L = 0) →
      ψ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 L) L).restrict ΦL] 0)
    (ι' : Type) (b' : ι' → AdelicGL2 (𝓞 L) L → ℂ) (cls' : ι' → HeckeEigensystem L ℂ)
    (hb' : ∀ i, cls' i ∈ cuspClasses L
          (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
          (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ₀ N SL ∧
        b' i ∈ isotypicCuspSubmodule L
          (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
          (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ₀ N SL (cls' i) ⊓ archCutSubmodule L tysL)
    (hb'n : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain L α β,
        b' i g * conj (b' i g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 1)
    (hb'o : ∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain L α β,
        b' i g * conj (b' j g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0)
    (hb's : ∀ π ∈ cuspClasses L
          (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
          (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ₀ N SL,
        {i | cls' i = π}.Finite ∧
        Submodule.span ℂ (b' '' {i | cls' i = π}) = isotypicCuspSubmodule L
          (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
          (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ₀ N SL π ⊓ archCutSubmodule L tysL)
    (hb'c : ∀ ψ : AdelicGL2 (𝓞 L) L → ℂ,
        IsSmoothCuspAutomorphicFnAt L
          (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
          (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)) ξ₀ ψ →
        Continuous ψ →
        (∀ g : AdelicGL2 (𝓞 L) L, ∀ u ∈
          (productionPinsOf L (AutomorphicForm.canonicalTruncationDomain L α β)
          (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
          (adelicBox L)).U N, ψ (g * u) = ψ g) →
        ψ ∈ archCutSubmodule L tysL →
        (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain L α β,
            ψ g * conj (b' i g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0) →
        ψ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 L) L).restrict (AutomorphicForm.canonicalTruncationDomain L α β)] 0)
    (φ φ' : AdelicGL2 (𝓞 L) L → ℂ)
    (hφ' : ∀ g : AdelicGL2 (𝓞 L) L, φ' g = φ g *
      (((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ))
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hfact : IsFactorizableTestFn L φ)
    (hbi : IsBiInvariantUnder L (levelOne (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) φ)
    (harch : IsArchBiFinite L tysL φ) :
    ∀ R : ℝ,
      IntegrableOn (fun x =>
              ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                        Ψ ∈ cuspClasses L
                          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                      ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
                x)))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      IntegrableOn (fun x =>
              ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' i : ι', convOp L φ' (b' i) x * conj (b' i y))
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x))))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∫ x in Φ₀,
              ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' Ψ : {Ψ : HeckeEigensystem L ℂ //
                        Ψ ∈ cuspClasses L
                          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL},
                      ∑ᶠ i : {i // cls i = Ψ.1}, twistedConvOp K L D σ φ (b i) x * conj (b i y))
                x)) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      (∫ x in Φ₀,
              ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => ((νZL (ΩL ∩ {z | NumberField.TateGlobal.ideleNorm L
                      (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 L) L z)) ∈ Set.Icc α β})).toReal : ℂ) *
                    ∑' i : ι', convOp L φ' (b' i) x * conj (b' i y))
                (AutomorphicForm.sigmaAdelicAct K L D σ.symm x))) ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) := by sorry
