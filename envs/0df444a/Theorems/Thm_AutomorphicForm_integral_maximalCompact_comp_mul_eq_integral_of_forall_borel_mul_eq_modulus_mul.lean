-- Prove2me | Theorems.Thm_AutomorphicForm_integral_maximalCompact_comp_mul_eq_integral_of_forall_borel_mul_eq_modulus_mul
-- name    : AutomorphicForm.integral_maximalCompact_comp_mul_eq_integral_of_forall_borel_mul_eq_modulus_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/0c444031-d63c-589e-99a7-321cbdffdf40
-- title:
--   Right invariance of the K-integral of modulus-equivariant functions
-- statement:
--   Let $K$ be a number field, with adele ring $\mathbb{A}=$ `AdeleRing (𝓞 K) K` and $\mathrm{GL}_2(\mathbb{A})$ given its Borel $\sigma$-algebra. Write $\alpha_m\colon \mathbb{A}^{\times}\to\mathbb{R}^{\times}$ for the monoid homomorphism obtained from the distributive Haar character `distribHaarChar (AdeleRing (𝓞 K) K)` of $\mathbb{A}$, whose values in $\mathbb{R}_{\ge 0}$ are pushed into $\mathbb{R}$ and viewed as units. The assertion is: for every continuous $\Phi\colon \mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$ such that for all $b$ lying in `adelicBorel (𝓞 K) K`, that is with matrix entry $b_{10}=0$, and all $g\in \mathrm{GL}_2(\mathbb{A})$ one has
--   $$\Phi(bg)=\frac{\alpha_m(b_{00})}{\alpha_m(b_{11})}\,\Phi(g),$$
--   where $b_{00}$ and $b_{11}$ are the two diagonal entries of $b$, regarded as ideles via `borelDiagFst` and `borelDiagSnd`, and for every $x\in \mathrm{GL}_2(\mathbb{A})$,
--   $$\int_{\mathbf{K}}\Phi(kx)\,dk=\int_{\mathbf{K}}\Phi(k)\,dk .$$
--   Here the integrals are Bochner integrals against `maximalCompactHaar K`, the Haar measure of the whole group `adelicMaximalCompact K`, the subgroup of those $k$ whose finite component lies in `finiteIntegralGL2 (𝓞 K) K` and whose archimedean component at each infinite place of $K$ is a row isometry.
--
--   This is the adelic form of the statement that integration over the standard maximal compact subgroup $\mathbf{K}$ furnishes a right $\mathrm{GL}_2(\mathbb{A})$-invariant functional on the continuous functions transforming under the Borel subgroup by its modulus character $b\mapsto |b_{11}/b_{22}|$, i.e. on continuous densities on $B(\mathbb{A})\backslash \mathrm{GL}_2(\mathbb{A})$; the proof cites the Iwasawa factorisation of the Haar measure of $\mathrm{GL}_2(\mathbb{A})$ together with its right invariance. It is used in the analytic estimates on induced sections and on $L^2$ inner products of automorphic forms, in particular in the non-vanishing and convolution bounds that invoke it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_maximalCompact_comp_mul_eq_integral_of_forall_borel_mul_eq_modulus_mul.lean

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

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.integral_maximalCompact_comp_mul_eq_integral_of_forall_borel_mul_eq_modulus_mul
    (K : Type) [Field K] [NumberField K] :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (Φ : AdelicGL2 (𝓞 K) K → ℂ) (_hΦc : Continuous Φ)
      (_hΦ : ∀ (b : AdelicGL2 (𝓞 K) K) (hb : b ∈ adelicBorel (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K),
        Φ (b * g) =
          ((((αm (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℝˣ) : ℝ) /
              ((αm (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℝˣ) : ℝ) : ℝ) : ℂ) * Φ g)
      (x : AdelicGL2 (𝓞 K) K),
      ∫ k, Φ ((k : AdelicGL2 (𝓞 K) K) * x) ∂(maximalCompactHaar K) =
        ∫ k, Φ (k : AdelicGL2 (𝓞 K) K) ∂(maximalCompactHaar K) := by sorry
