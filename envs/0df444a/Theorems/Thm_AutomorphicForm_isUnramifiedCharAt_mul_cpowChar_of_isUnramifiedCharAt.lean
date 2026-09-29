-- Prove2me | Theorems.Thm_AutomorphicForm_isUnramifiedCharAt_mul_cpowChar_of_isUnramifiedCharAt
-- name    : AutomorphicForm.isUnramifiedCharAt_mul_cpowChar_of_isUnramifiedCharAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/8abd6a40-3581-5ec9-8b4b-289c5c5e0a93
-- title:
--   Twisting by a complex power of the idelic modulus preserves unramifiedness
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal O_K$ and adele ring $\mathbb A_K$. Write $\alpha_m \colon \mathbb A_K^\times \to \mathbb R^\times$ for the monoid homomorphism on units induced by the Haar-scaling character `distribHaarChar` of $\mathbb A_K$ (a map to $\mathbb R_{\ge 0}$, pushed into $\mathbb R$ and then into units), the adele ring carrying its Borel $\sigma$-algebra. Assume $\alpha_m(x) > 0$ for all $x$. Then for every monoid homomorphism $\chi \colon \mathbb A_K^\times \to \mathbb C^\times$, every $s \in \mathbb C$ and every height-one prime $v$ of $\mathcal O_K$: if $\chi$ satisfies `IsUnramifiedCharAt` at $v$, i.e. $\chi$ sends to $1$ every unit $t$ of the completion $K_v$ such that both $t$ and $t^{-1}$ lie in the valuation ring of $K_v$, $t$ being viewed as an idele through the local inclusion $K_v^\times \hookrightarrow \mathbb A_{K,\mathrm f}^\times \hookrightarrow \mathbb A_K^\times$, then the product character $\chi \cdot \mathrm{cpowChar}(\alpha_m, s)$ is likewise unramified at $v$, where $\mathrm{cpowChar}(\alpha_m, s)$ is the character $x \mapsto \alpha_m(x)^s$ (complex power of a positive real).
--
--   This is the elementary stability statement, in Tate's theory of global zeta functions, that unramifiedness of an idele class character at a finite place is preserved by twisting with a complex power of the idelic modulus, the modulus being realised here as the module of the multiplication action on Haar measure of the adeles. It is used when characters occurring in the continuous spectrum are twisted by powers of the modulus and one must retain unramifiedness outside a fixed finite set of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isUnramifiedCharAt_mul_cpowChar_of_isUnramifiedCharAt.lean

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

theorem AutomorphicForm.isUnramifiedCharAt_mul_cpowChar_of_isUnramifiedCharAt
    (K : Type) [Field K] [NumberField K] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) (v : HeightOneSpectrum (𝓞 K)),
      NumberField.TateGlobal.IsUnramifiedCharAt χ v →
      NumberField.TateGlobal.IsUnramifiedCharAt (χ * cpowChar αm hαm s) v := by sorry
