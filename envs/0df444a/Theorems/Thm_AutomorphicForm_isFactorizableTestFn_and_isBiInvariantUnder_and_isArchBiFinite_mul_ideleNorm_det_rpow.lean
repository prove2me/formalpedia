-- Prove2me | Theorems.Thm_AutomorphicForm_isFactorizableTestFn_and_isBiInvariantUnder_and_isArchBiFinite_mul_ideleNorm_det_rpow
-- name    : AutomorphicForm.isFactorizableTestFn_and_isBiInvariantUnder_and_isArchBiFinite_mul_ideleNorm_det_rpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/45529860-233e-520a-a5e3-4fe545de3c41
-- title:
--   Twisting a GL₂ test function by ‖det‖^{w/2}
-- statement:
--   Let $K$ be a number field, $N$ an ideal of $\mathcal O_K$, $\mathrm{tysK}$ an archimedean type family for $K$ (the data of a cardinality $\mathrm{card}\,w$ for each infinite place $w$ together with, for each $i<\mathrm{card}\,w$, a representation of the relevant row-isometry subgroup of $K_w$ on a finite-dimensional complex space), and $w\in\mathbb R$. Let $f\colon \mathrm{GL}_2(\mathbb A_K)\to\mathbb C$ be continuous with compact support, factorizable in the sense that $f(g)=f_\infty(\mathrm{glArch}\,g)\cdot f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ for some compactly supported $f_\infty$ on $\mathrm{GL}_2(K\otimes\mathbb R)$ arising as a $C^\infty$ function of the archimedean matrix entries and some locally constant compactly supported $f_{\mathrm{fin}}$ on $\mathrm{GL}_2(\mathbb A_{K,\mathrm{fin}})$, bi-invariant under the subgroup $U=\mathrm{principalLevel}(\mathcal O_K,K,N)\cap\ker(\mathrm{glArch})$ (i.e. $f(ug)=f(g)=f(gu)$ for all $u\in U$ and all $g$, where $\mathrm{principalLevel}$ is the intersection of $\mathrm{levelOne}$ at $N$ with its conjugate by the Weyl element), and archimedean bi-finite of type $\mathrm{tysK}$, meaning $g\mapsto f(g^{-1})$ lies in `archCutSubmodule` and $f$ lies in `archDualCutSubmodule` for $\mathrm{tysK}$. Then the twisted function $g\mapsto f(g)\cdot\|\det g\|^{w/2}$, where $\|\cdot\|$ is the idele norm given by the distributive Haar character of $\mathbb A_K$, again has all five properties: continuity, compact support, factorizability, bi-invariance under the same $U$, and archimedean bi-finiteness of the same type family.
--
--   This is the elementary stability of the space of $\mathrm{GL}_2$ adelic test functions under multiplication by the unramified character $\|\det\|^{w/2}$, which is continuous, factors over the places, and is trivial on the relevant compact open subgroups. It is used when the spectral and geometric sides of the adelic trace/Poincaré-series identities are shifted by a power of the idele norm of the determinant, in the three statements that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isFactorizableTestFn_and_isBiInvariantUnder_and_isArchBiFinite_mul_ideleNorm_det_rpow.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.isFactorizableTestFn_and_isBiInvariantUnder_and_isArchBiFinite_mul_ideleNorm_det_rpow
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) (w : ℝ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (_hfact : IsFactorizableTestFn K f)
    (_hbi : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f)
    (_harch : IsArchBiFinite K tysK f) :
    Continuous (fun g : AdelicGL2 (𝓞 K) K => f g *
        (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) ∧
    HasCompactSupport (fun g : AdelicGL2 (𝓞 K) K => f g *
        (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) ∧
    IsFactorizableTestFn K (fun g : AdelicGL2 (𝓞 K) K => f g *
        (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) ∧
    IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun g : AdelicGL2 (𝓞 K) K => f g *
        (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) ∧
    IsArchBiFinite K tysK (fun g : AdelicGL2 (𝓞 K) K => f g *
        (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) := by sorry
