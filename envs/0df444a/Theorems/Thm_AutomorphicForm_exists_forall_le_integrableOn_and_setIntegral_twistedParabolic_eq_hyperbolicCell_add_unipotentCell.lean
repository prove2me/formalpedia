-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_le_integrableOn_and_setIntegral_twistedParabolic_eq_hyperbolicCell_add_unipotentCell
-- name    : AutomorphicForm.exists_forall_le_integrableOn_and_setIntegral_twistedParabolic_eq_hyperbolicCell_add_unipotentCell
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/377ec42a-b04a-58db-aa49-555761f61a13
-- title:
--   Hyperbolic–unipotent splitting of the truncated twisted parabolic term
-- statement:
--   Throughout, $K \subseteq L$ are number fields with $L/K$ finite Galois, and $\mathrm{GL}_2(\mathbb{A}_L)$ denotes `AdelicGL2 (𝓞 L) L`, the general linear group of degree $2$ over the adele ring of $L$, equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar (Fin 2) (𝓞 L) L`. The map `globalPoints (𝓞 L) L` is the entrywise inclusion $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A}_L)$, written $\iota$ below, and `centralScalar (𝓞 L) L` sends an idele $z$ to the scalar matrix $\mathrm{diag}(z,z)$, written $Z(z)$.
--
--   The data are as follows. Real numbers $\alpha, \beta$ with $0 < \alpha$ and $\alpha < \beta$; a set $\Phi_L \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ with the hypothesis `hΦs` that $\Phi_L$ lies in the determinant slab $\{g : \|\det g\| \in [\alpha,\beta]\}$, where $\|\cdot\|$ is the idele norm [`NumberField.TateGlobal.ideleNorm L`](def/NumberField_TateGlobalZeta.html#L19) (the modulus of the scaling action on additive Haar measure of $\mathbb{A}_L$), and the hypothesis `hΦ` that $\Phi_L$ is a fundamental domain for the image of $\iota$ acting on the Haar measure of $\mathrm{GL}_2(\mathbb{A}_L)$ restricted to that slab. Further: a measurable space and Borel space structure on the idele group $\mathbb{A}_L^\times$, a Haar measure $\nu_{Z,L}$ on it, and a set $\Omega_L \subseteq \mathbb{A}_L^\times$ which by `hΩL` is a fundamental domain for the image of $L^\times$ in $\mathbb{A}_L^\times$ with respect to $\nu_{Z,L}$. Next, a datum $D$ of type [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), that is, a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ which is continuous in each component and compatible with the diagonal embedding of $L$; an element $\sigma \in \mathrm{Gal}(L/K)$ with the hypothesis `hgen` that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$. The induced entrywise automorphism `sigmaAdelicAct K L D σ` of $\mathrm{GL}_2(\mathbb{A}_L)$ is written $\sigma_{\mathbb{A}}$. Next, a character $\xi_L$ of the top subgroup of $\mathbb{A}_L^\times$ with values in $\mathbb{C}^\times$, subject to `hξc`, continuity of $z \mapsto \xi_L(z)$ as a complex-valued function, and `hξt`, triviality of $\xi_L$ on the image of $L^\times$. Finally a test function: $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ with `hφ` continuity and `hφc` compact support; a finite set $S$ of height one primes of $\mathcal{O}_K$; functions $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adeles of $L$, $\varphi_S(v)$ on $\mathrm{GL}_2(L \otimes_K K_v)$ for each height one prime $v$ of $\mathcal{O}_K$, and $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$; and the hypothesis `hfac`, that $(\varphi, \varphi_a, \varphi_f, \varphi_S)$ is a semi-local factorisation relative to $S$: $\varphi_a$ is an archimedean test factor (given by a smooth function of the mixed-space matrix entries, with compact support), $\varphi_f$ is locally constant with compact support, each $\varphi_S(v)$ for $v \in S$ is locally constant with compact support, $\varphi_f(h) = \prod_{v \in S} \varphi_S(v)$ evaluated at the $v$-semi-local component of $h$ whenever all semi-local components of $h$ outside $S$ lie in the corresponding integral units set, $\varphi_f(h) = 0$ as soon as some semi-local component outside $S$ fails to be integral, and $\varphi(g) = \varphi_a(g_\infty)\,\varphi_f(g_{\mathrm{fin}})$ for all $g$.
--
--   Two kinds of index set occur. For a set $C \subseteq \mathrm{GL}_2(K)$ put
--   $$\mathcal{T}(C) = \{\delta \in \mathrm{GL}_2(L) \ :\ \exists\, \gamma \in C,\ \mathrm{normClassMap}\,\mathrm{hgen}\,[\delta]_{\sigma} = [\gamma]\},$$
--   where $[\delta]_\sigma$ is the class of $\delta$ for $\sigma$-twisted conjugacy and `normClassMap hgen` is the induced map from $\sigma$-twisted classes to ordinary conjugacy classes in $\mathrm{GL}_2(K)$. The two cells used are `hyperbolicCell K`, the set of $\gamma$ whose characteristic polynomial is $(X-a)(X-b)$ with $a \neq b$, and `unipotentCell K`, the set of $\gamma$ of non-central type whose characteristic polynomial is $(X-a)^2$. The Borel index sets are $B_{\neq} = \{\gamma \in \mathrm{GL}_2(L) : \gamma_{10} = 0,\ N_{L/K}(\gamma_{00}/\gamma_{11}) \neq 1\}$ and $B_{=}$, the same with $N_{L/K}(\gamma_{00}/\gamma_{11}) = 1$, where $N_{L/K}$ is `Algebra.norm K`.
--
--   For a set $\mathcal{D} \subseteq \mathrm{GL}_2(L)$ of summation indices, a set $B$ of Borel indices, a real $R$, and $x \in \mathrm{GL}_2(\mathbb{A}_L)$, $z \in \mathbb{A}_L^\times$, set
--   $$F_{\mathcal{D},B,R}(x,z) = \xi_L(z)\Big(\textstyle\sum^{\mathrm{f}}_{\delta \in \mathcal{D}} \varphi\big(x^{-1}\,\iota(\delta)\,\sigma_{\mathbb{A}}(Z(z)x)\big) \;-\; \mathbf{1}_{H_R}\!\big(Z(z)x\big)\, c_B(x, Z(z)x)\Big),$$
--   where the sums $\sum^{\mathrm{f}}$ are unordered sums over the indicated sets, $H_R = \{g : \exp R < \mathrm{adelicHeight}\,L\,(g)\}$ is the high set of the adelic height (the product of the archimedean height of the infinite component and the finite height of the finite component), and $c_B$ is the constant term
--   $$c_B(x,g) = \int_{\mathbb{A}_L} \ \textstyle\sum^{\mathrm{f}}_{\delta \in B} \varphi\big(x^{-1}\,\iota(\delta)\,\sigma_{\mathbb{A}}(n(t)\,g)\big)\ d\nu(t), \qquad n(t) = \begin{pmatrix} 1 & t \\ 0 & 1\end{pmatrix},$$
--   the measure $\nu$ and the ambient $\sigma$-algebra on $\mathbb{A}_L$ being the `nS` and `ν` fields of `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)`, namely the Borel structure on $\mathbb{A}_L$ and the additive Haar measure of $\mathbb{A}_L$ conditioned on the adelic box `adelicBox L`. In the same notation, write $F^{\mathrm{tot}}_{R}(x,z)$ for the variant of $F_{\mathcal{D},B,R}$ in which $\mathcal{D} = \mathcal{T}(\text{hyperbolic} \cup \text{unipotent})$, i.e. the set of $\delta$ whose norm class is the conjugacy class of some $\gamma$ lying in the hyperbolic cell or in the unipotent cell, and in which the function whose constant term is taken is the full twisted kernel $y \mapsto \mathrm{twistedAdelicKernel}\,L\,\sigma_{\mathbb{A}}\,\varphi\,x\,y = \sum^{\mathrm{f}}_{\gamma \in \mathrm{GL}_2(L)} \varphi(x^{-1}\iota(\gamma)\sigma_{\mathbb{A}}(y))$, the sum now being over all of $\mathrm{GL}_2(L)$.
--
--   The assertion is the existence of a real $R_0$ such that for every real $R \geq R_0$ the following five statements hold, with $\Phi_0 = \mathrm{canonicalTruncationDomain}\,L\,\alpha\,\beta$ (the third component of the canonically chosen truncation datum for $L, \alpha, \beta$, and the empty set if no such datum exists).
--
--   First, for every $x \in \mathrm{GL}_2(\mathbb{A}_L)$ the function $z \mapsto F_{\mathcal{T}(\text{hyperbolicCell } K),\,B_{\neq},\,R}(x,z)$ is integrable on $\Omega_L$ with respect to $\nu_{Z,L}$. Second, the function $x \mapsto \int_{\Omega_L} F_{\mathcal{T}(\text{hyperbolicCell } K),\,B_{\neq},\,R}(x,z)\, d\nu_{Z,L}(z)$ is integrable on $\Phi_0$ with respect to the Haar measure of $\mathrm{GL}_2(\mathbb{A}_L)$. Third, for every $x$ the function $z \mapsto F_{\mathcal{T}(\text{unipotentCell } K),\,B_{=},\,R}(x,z)$ is integrable on $\Omega_L$ with respect to $\nu_{Z,L}$. Fourth, the function $x \mapsto \int_{\Omega_L} F_{\mathcal{T}(\text{unipotentCell } K),\,B_{=},\,R}(x,z)\, d\nu_{Z,L}(z)$ is integrable on $\Phi_0$ with respect to the Haar measure. Fifth, the identity
--   $$\int_{\Phi_0}\int_{\Omega_L} F^{\mathrm{tot}}_{R}(x,z)\, d\nu_{Z,L}(z)\, dx = \int_{\Phi_0}\int_{\Omega_L} F_{\mathcal{T}(\text{hyperbolicCell } K),\,B_{\neq},\,R}(x,z)\, d\nu_{Z,L}(z)\, dx + \int_{\Phi_0}\int_{\Omega_L} F_{\mathcal{T}(\text{unipotentCell } K),\,B_{=},\,R}(x,z)\, d\nu_{Z,L}(z)\, dx$$
--   holds, the outer integrals being taken against `adelicGLHaar (Fin 2) (𝓞 L) L`.
--
--   This is the splitting of the truncated parabolic term of the $\sigma$-twisted Arthur–Selberg trace formula for $\mathrm{GL}_2$ over $L/K$ into its hyperbolic and unipotent contributions: on the level of the combined twisted cell, both the summation over twisted classes and the truncating constant term separate according to whether the norm of the diagonal ratio of an upper-triangular element is $1$, together with the absolute integrability of each piece over the folded canonical truncation domain. It feeds the comparison of parabolic intercepts used further along in the twisted trace formula, being cited by [`AutomorphicForm.exists_continuous_noAtomicMass_intercept_parabolic_sub_finrank_mul_const_mul_sum_intercept_parabolic_eq_uniform`](thm.html#AutomorphicForm.exists_continuous_noAtomicMass_intercept_parabolic_sub_finrank_mul_const_mul_sum_intercept_parabolic_eq_uniform).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_le_integrableOn_and_setIntegral_twistedParabolic_eq_hyperbolicCell_add_unipotentCell.lean

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
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel
open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_forall_le_integrableOn_and_setIntegral_twistedParabolic_eq_hyperbolicCell_add_unipotentCell
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
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
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ)
    (hfac : IsSemiLocalFactorization K L S φ φa φf φS) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∀ x : AdelicGL2 (𝓞 L) L, IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL))
        (AutomorphicForm.canonicalTruncationDomain L α β) (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∀ x : AdelicGL2 (𝓞 L) L, IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL))
        (AutomorphicForm.canonicalTruncationDomain L α β) (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      ∫ x in AutomorphicForm.canonicalTruncationDomain L α β,
          (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
                (γ ∈ AutomorphicForm.hyperbolicCell K ∨ γ ∈ AutomorphicForm.unipotentCell K) ∧
                LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
              Set.indicator
                (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                  (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                    (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y =>
                    AutomorphicForm.twistedAdelicKernel L (AutomorphicForm.sigmaAdelicAct K L D σ) φ x y))
                (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      (∫ x in AutomorphicForm.canonicalTruncationDomain L α β, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) +
      (∫ x in AutomorphicForm.canonicalTruncationDomain L α β, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) := by sorry
