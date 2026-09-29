-- Prove2me | Theorems.Thm_AutomorphicForm_constantTerm_convOp_eq_zero_of_ae_constantTerm_eq_zero_of_isAutomorphicFnAt
-- name    : AutomorphicForm.constantTerm_convOp_eq_zero_of_ae_constantTerm_eq_zero_of_isAutomorphicFnAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/9a4537b9-89cb-5c55-8cf6-c1e24bb97f1e
-- title:
--   Smoothing upgrades almost-everywhere cuspidality to pointwise vanishing
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta$ be reals with $0<\alpha<\beta$, and let $\xi_K$ be a homomorphism from the full subgroup $\top$ of the idele units $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ whose associated complex-valued function on $(\mathbb{A}_K)^\times$ is continuous. Write $P$ for the carrier pins `productionPinsOf` attached to $K$ with domain the canonical truncation domain `canonicalTruncationDomain K α β`, level assignment $M \mapsto \mathrm{principalLevel}(M) \sqcap$ `finiteAdelicGL2Subgroup K`, Hecke generators $v \mapsto$ `heckeGen`, and box `adelicBox K` $=\{x : x_\infty \in \mathrm{infiniteBox}(K),\ x_{\mathrm{fin}} \in \widehat{\mathcal{O}}_K\}$; thus $P$ carries the Borel structure and adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$, central subgroup $Z=\top$, the Borel structure on $\mathbb{A}_K$, and the measure $P.\nu$ obtained by conditioning adelic additive Haar measure on `adelicBox K`. Let $u : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ satisfy `IsAutomorphicFnAt` for $P$ and $\xi_K$, i.e. the predicate `LsXiMember` for these data, and let $f : \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous with compact support. Then: if for `adelicGLHaar`-almost every $g$ the constant term `constantTerm P.ν unipotentGL2 u g` vanishes — the integral against $P.\nu$ of the integrand formed from $u$, $g$ and the unipotent matrices $\mathrm{unipotentGL2}(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$ — then the corresponding constant term of `convOp K f u` $=$ `rightConv K u f` vanishes at every $g \in \mathrm{GL}_2(\mathbb{A}_K)$.
--
--   This is the passage from almost-everywhere to pointwise cuspidality by smoothing: convolving an $L^2$ automorphic function on the right by a continuous compactly supported test function makes its unipotent constant term vanish identically. It feeds the construction of smooth cusp forms from $L^2$ automorphic functions and the inner-product computations for the projection onto continuous vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_constantTerm_convOp_eq_zero_of_ae_constantTerm_eq_zero_of_isAutomorphicFnAt.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.constantTerm_convOp_eq_zero_of_ae_constantTerm_eq_zero_of_isAutomorphicFnAt
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (u : AdelicGL2 (𝓞 K) K → ℂ) (_hu : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    :
    letI := adeleBorel (𝓞 K) K
    (∀ᵐ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K), constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 u g = 0) →
    ∀ g : AdelicGL2 (𝓞 K) K, constantTerm (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).ν unipotentGL2 (convOp K f u) g = 0 := by sorry
