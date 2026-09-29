-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_le_integrableOn_twistedHyperbolicCell_and_twistedUnipotentCell_sub_indicator_constantTerm
-- name    : AutomorphicForm.exists_forall_le_integrableOn_twistedHyperbolicCell_and_twistedUnipotentCell_sub_indicator_constantTerm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/7055b6af-85e5-52da-a0a1-dd9ee6f58707
-- title:
--   Integrability of the truncated twisted hyperbolic and unipotent kernels
-- statement:
--   Fix number fields $K \subseteq L$ with $L/K$ finite and Galois, and real numbers $\alpha, \beta$ with $0 < \alpha$ (`hα`) and $\alpha < \beta$ (`hαβ`).
--
--   The data are as follows.
--
--   *Fundamental domain in the determinant slab.* A set $\Phi_L \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ (here `AdelicGL2 (𝓞 L) L` is $\mathrm{GL}_2$ of the adele ring of $L$) subject to two hypotheses: `hΦs` says $\Phi_L$ is contained in the slab $\{g : \mathrm{ideleNorm}_L(\det g) \in [\alpha,\beta]\}$, where [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19) is the module of the scaling action of an idele on the adeles; `hΦ` says $\Phi_L$ is a fundamental domain for the range of `globalPoints`, the image of $\mathrm{GL}_2(L)$ in $\mathrm{GL}_2(\mathbb{A}_L)$ under the structure map, with respect to the adelic Haar measure `adelicGLHaar (Fin 2) (𝓞 L) L` restricted to that slab.
--
--   *Centre.* A measurable and Borel structure on the idele group $\mathbb{A}_L^\times$, a Haar measure $\nu_{Z,L}$ on it, and a set $\Omega_L \subseteq \mathbb{A}_L^\times$ which by `hΩL` is a fundamental domain for the range of $L^\times \to \mathbb{A}_L^\times$ with respect to $\nu_{Z,L}$.
--
--   *Twisting data.* A descent datum $D$ of type [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), that is a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ which is continuous for each element and compatible with the algebra map $L \to \mathbb{A}_L$; an element $\sigma \in \mathrm{Gal}(L/K)$ with `hgen` asserting that every $\tau \in \mathrm{Gal}(L/K)$ lies in the group of integer powers of $\sigma$. Write $\sigma_D =$ `sigmaAdelicAct K L D σ` for the induced automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$, obtained by applying $D(\sigma)$ entrywise.
--
--   *Character.* A homomorphism $\xi_L$ from the top subgroup of $\mathbb{A}_L^\times$ to $\mathbb{C}^\times$, with `hξc` the continuity of $z \mapsto \xi_L(z) \in \mathbb{C}$ and `hξt` its triviality on the image of $L^\times$.
--
--   *Test function.* A function $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ which is continuous (`hφ`) and compactly supported (`hφc`), together with a finite set $S$ of nonzero primes of $\mathcal{O}_K$ and factors $\varphi_\infty$ on $\mathrm{GL}_2$ of the infinite adeles of $L$, $\varphi_v$ on $\mathrm{GL}_2(L \otimes_K K_v)$ for each prime $v$ of $K$, and $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$. The hypothesis `hfac`, `IsSemiLocalFactorization K L S φ φa φf φS` (six clauses, summarised here), requires: $\varphi_\infty$ is an archimedean test factor, namely compactly supported and given by a smooth function of the matrix entries viewed in the mixed space of $L$; $\varphi_f$ is locally constant with compact support; for each $v \in S$ the factor $\varphi_v$ is locally constant with compact support; $\varphi_f(h) = \prod_{v \in S} \varphi_v(h_v)$ whenever all semi-local components of $h$ outside $S$ lie in the semi-local integral units set, while $\varphi_f(h) = 0$ as soon as some semi-local component outside $S$ fails to lie there; and $\varphi(g) = \varphi_\infty(g_\infty)\,\varphi_f(g_f)$ for all $g$.
--
--   To state the conclusion, introduce for subsets $I, J \subseteq \mathrm{GL}_2(L)$, a real $R$, an element $x \in \mathrm{GL}_2(\mathbb{A}_L)$ and an idele $z$ the quantity
--   $$k_{I,J,R}(x,z) \;=\; \xi_L(z)\Bigl( \sum^{\mathrm{f}}_{\delta \in I} \varphi\bigl(x^{-1}\,\delta\,\sigma_D(z x)\bigr) \;-\; \mathbf{1}_{\{H > e^{R}\}}(z x)\cdot \bigl(\textstyle\int\bigr)_{J}(z x)\Bigr),$$
--   where: $\delta$ is mapped into $\mathrm{GL}_2(\mathbb{A}_L)$ by `globalPoints`, $z$ acts through `centralScalar`, the scalar matrix with entries $z$, and $\sum^{\mathrm{f}}$ is the finsum over the indicated set; $H =$ [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158) is the adelic height, the product of the archimedean height of the infinite part and the finite height of the finite part, and $\{H > e^R\}$ is `highSet H (Real.exp R)`; and $(\int)_J$ is the constant term [`AutomorphicForm.constantTerm`](def/AutomorphicForm_ConstantTerm.html#L47) of the function $y \mapsto \sum^{\mathrm{f}}_{\delta \in J} \varphi(x^{-1}\delta\,\sigma_D(y))$ along the unipotent one-parameter family $t \mapsto \begin{pmatrix}1 & t\\ 0 & 1\end{pmatrix}$, that is $g \mapsto \int_{\mathbb{A}_L} \sum^{\mathrm{f}}_{\delta \in J}\varphi(x^{-1}\delta\,\sigma_D(u(t)g))\,d\nu(t)$, evaluated at $g = z x$. The measurable structure and the measure $\nu$ used here are the `nS` and `ν` fields of the record `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)`, namely the Borel structure `adeleBorel (𝓞 L) L` on $\mathbb{A}_L$ and the additive Haar measure `adelicAddHaar (𝓞 L) L` conditioned on the adelic box `adelicBox L`.
--
--   The index sets occurring are, for the hyperbolic cell,
--   $$I_{\mathrm{hyp}} = \{\delta \in \mathrm{GL}_2(L) : \exists\, \gamma \in \mathrm{GL}_2(K)\ \text{with charpoly } (X-a)(X-b),\ a \neq b,\ \text{and } \mathrm{normClassMap}_{hgen}([\delta]_\sigma) = [\gamma]\},$$
--   where $[\delta]_\sigma$ is the class of $\delta$ for $\sigma$-conjugacy and [`LT.TwistedNorm.normClassMap hgen`](def/TwistedNormClasses.html#L766) sends it to the ordinary conjugacy class in $\mathrm{GL}_2(K)$ of a norm representative, and
--   $$J_{\mathrm{hyp}} = \{\gamma \in \mathrm{GL}_2(L) : \gamma_{10} = 0,\ N_{L/K}(\gamma_{00}/\gamma_{11}) \neq 1\};$$
--   and for the unipotent cell, $I_{\mathrm{unip}}$ defined in the same way but with $\gamma$ required to lie in `unipotentCell K`, i.e. $\gamma$ is not of central type and its characteristic polynomial is $(X-a)^2$ for some $a \in K$, and
--   $$J_{\mathrm{unip}} = \{\gamma \in \mathrm{GL}_2(L) : \gamma_{10} = 0,\ N_{L/K}(\gamma_{00}/\gamma_{11}) = 1\}.$$
--
--   The assertion is: there exists $R_0 \in \mathbb{R}$ such that for every $R \geq R_0$ the following four statements hold.
--
--   (i) For every $x \in \mathrm{GL}_2(\mathbb{A}_L)$, the function $z \mapsto k_{I_{\mathrm{hyp}},J_{\mathrm{hyp}},R}(x,z)$ is integrable on $\Omega_L$ with respect to $\nu_{Z,L}$.
--
--   (ii) The function $x \mapsto \int_{\Omega_L} k_{I_{\mathrm{hyp}},J_{\mathrm{hyp}},R}(x,z)\,d\nu_{Z,L}(z)$ is integrable on [`AutomorphicForm.canonicalTruncationDomain L α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) — the third component of the canonically chosen truncation datum for $L$, $\alpha$, $\beta$ (the empty set if no such datum exists) — with respect to `adelicGLHaar (Fin 2) (𝓞 L) L`.
--
--   (iii) For every $x \in \mathrm{GL}_2(\mathbb{A}_L)$, the function $z \mapsto k_{I_{\mathrm{unip}},J_{\mathrm{unip}},R}(x,z)$ is integrable on $\Omega_L$ with respect to $\nu_{Z,L}$.
--
--   (iv) The function $x \mapsto \int_{\Omega_L} k_{I_{\mathrm{unip}},J_{\mathrm{unip}},R}(x,z)\,d\nu_{Z,L}(z)$ is integrable on [`AutomorphicForm.canonicalTruncationDomain L α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32) with respect to `adelicGLHaar (Fin 2) (𝓞 L) L`.
--
--   This is the twisted, $\mathrm{GL}_2$ form of the cell-by-cell absolute convergence of Arthur's truncated kernel: for the hyperbolic and for the unipotent twisted norm classes, the difference between the cell sum and the truncated constant term of its Borel part is integrable over the central fundamental domain and, after integration in the centre, over the canonical truncation domain. It supplies the integrability halves of the splitting of the twisted parabolic term into hyperbolic and unipotent contributions, and is used again in the comparison of unipotent terms for matching test functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_le_integrableOn_twistedHyperbolicCell_and_twistedUnipotentCell_sub_indicator_constantTerm.lean

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

theorem AutomorphicForm.exists_forall_le_integrableOn_twistedHyperbolicCell_and_twistedUnipotentCell_sub_indicator_constantTerm
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
        (AutomorphicForm.canonicalTruncationDomain L α β) (adelicGLHaar (Fin 2) (𝓞 L) L) := by sorry
