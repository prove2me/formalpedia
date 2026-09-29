-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_eq_zero_of_forall_residualSpan_of_closure
-- name    : AutomorphicForm.setIntegral_mul_conj_eq_zero_of_forall_residualSpan_of_closure
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/ef65ad6d-af1e-55e8-983f-2eb67a805615
-- title:
--   Orthogonality extends to the L²-closure of the residual span
-- statement:
--   Let $K$ be a number field and $\alpha,\beta$ real numbers with $0<\alpha<\beta$; let $\Phi_0 =$ `canonicalTruncationDomain K α β` be the subset of $\mathrm{GL}_2(\mathbb{A}_K)$ attached to the canonical truncation datum for $\alpha,\beta$ (a chosen witness of `IsTruncationDatum`, and $\emptyset$ if none exists), and let $\mu =$ `adelicGLHaar (Fin 2) (𝓞 K) K` be the Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$ for its Borel structure. Fix a homomorphism $\xi_K$ from the full unit group $(\mathbb{A}_K)^\times$ (as the subgroup $\top$) to $\mathbb{C}^\times$, and write $P$ for the carrier pins `productionPinsOf` built from $\Phi_0$, the level subgroups $M \mapsto$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, the Hecke elements $v \mapsto$ `heckeGen (𝓞 K) K v` and the box `adelicBox K`; the automorphy predicate `IsAutomorphicFnAt K P ξK` depends on the Borel structure, the measure $\mu$, the domain $\Phi_0$ and the central subgroup $\top$ recorded in $P$. Let $x,y : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ both satisfy `IsAutomorphicFnAt K P ξK`. Assume that for every $h$ satisfying `IsAutomorphicFnAt K P ξK` and lying in the residual span, i.e. in the $\mathbb{C}$-span of the functions $g \mapsto \chi(\det g)$ for characters $\chi$ of $(\mathbb{A}_K)^\times$ with $\chi(z)^2 = \xi_K(z)$ for all $z$, one has $\int_{\Phi_0} x\,\overline{h}\,d\mu = 0$; and assume that for every $\varepsilon>0$ there is a $q$ in that residual span satisfying `IsAutomorphicFnAt K P ξK` with $\lVert y-q\rVert_{L^2(\mu|_{\Phi_0})} < \varepsilon$. Then $\int_{\Phi_0} x\,\overline{y}\,d\mu = 0$ and $\int_{\Phi_0} y\,\overline{x}\,d\mu = 0$.
--
--   This is the standard continuity statement that a vector orthogonal to a subset of an $L^2$ space is orthogonal to its closure, in the form needed for the residual span of $\chi\circ\det$ characters on a truncated adelic domain. It serves as a bookkeeping step for the residual-projection clauses of the spectral decomposition, and is used by [`AutomorphicForm.setIntegral_continuousPart_mul_conj_convOp_continuousPart_eq_sub_of_pseudoEisenstein_threeWay`](thm.html#AutomorphicForm.setIntegral_continuousPart_mul_conj_convOp_continuousPart_eq_sub_of_pseudoEisenstein_threeWay).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_mul_conj_eq_zero_of_forall_residualSpan_of_closure.lean

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
import Definitions.Def_AutomorphicForm_ResidualSpan

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.setIntegral_mul_conj_eq_zero_of_forall_residualSpan_of_closure
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (x y : AdelicGL2 (𝓞 K) K → ℂ)
    (_hx : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK x)
    (_hxo : ∀ h : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK h →
        h ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, x g * conj (h g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
    (_hy : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK y)
    (_hyc : ∀ ε > (0:ℝ), ∃ q ∈ AutomorphicForm.residualSpan (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK,
        IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK q ∧
        eLpNorm (y - q) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) < ENNReal.ofReal ε) :
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, x g * conj (y g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 ∧
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β, y g * conj (x g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by sorry
