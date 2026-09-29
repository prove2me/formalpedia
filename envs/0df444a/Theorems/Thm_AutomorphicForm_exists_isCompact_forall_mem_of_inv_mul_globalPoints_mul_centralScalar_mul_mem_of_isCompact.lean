-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_forall_mem_of_inv_mul_globalPoints_mul_centralScalar_mul_mem_of_isCompact
-- name    : AutomorphicForm.exists_isCompact_forall_mem_of_inv_mul_globalPoints_mul_centralScalar_mul_mem_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/3f577ed9-960f-529c-ba5c-87ee783db05e
-- title:
--   Properness of the centre of GL₂(A_K)
-- statement:
--   Let $K$ be a number field (a field with the `NumberField` structure), let $C$, $C_x$, $C_y$ be compact subsets of $GL_2(\mathbb{A}_K)$, the general linear group of degree $2$ over the adele ring of $K$ (topologised as a unit group of matrices, with the Borel $\sigma$-algebra coming from that topology), and let $\gamma \in GL_2(K)$. Here `globalPoints` denotes the group homomorphism $GL_2(K) \to GL_2(\mathbb{A}_K)$ induced entrywise by the structure map $K \to \mathbb{A}_K$, and `centralScalar` denotes the homomorphism $\mathbb{A}_K^\times \to GL_2(\mathbb{A}_K)$ sending an idele $z$ to the scalar matrix $z \cdot 1$. The assertion is that there exists a subset $S$ of the idele group $\mathbb{A}_K^\times$ which is compact and has the property that every $z \in \mathbb{A}_K^\times$ for which one can find $x \in C_x$ and $y \in C_y$ with $x^{-1}\,\gamma\,(z\cdot 1)\,y \in C$ (products taken in $GL_2(\mathbb{A}_K)$, with $\gamma$ mapped in by `globalPoints`) lies in $S$. Only this one inclusion is claimed: no converse, and no description of $S$ beyond its compactness.
--
--   This is the properness statement for the central embedding $\mathbb{A}_K^\times \hookrightarrow GL_2(\mathbb{A}_K)$: the set of central ideles whose scalar matrix moves a fixed rational point $\gamma$ into a compact set, modulo compact two-sided translation, is relatively compact. It is what converts a central integral $\int_{\mathbb{A}_K^\times} \xi(z) f(x^{-1}\gamma z y)\,dz$ of a compactly supported function into an integral over a fixed compact set, and it is used in the construction of automorphic functions from windowed Siegel data, by [`AutomorphicForm.continuous_uncurry_finsum_integral_centralScalar_mul_apply_inv_mul_globalPoints_mul_centralScalar_mul`](thm.html#AutomorphicForm.continuous_uncurry_finsum_integral_centralScalar_mul_apply_inv_mul_globalPoints_mul_centralScalar_mul), [`AutomorphicForm.isAutomorphicFnAt_finsum_integral_indicator_canonicalTruncationDomain`](thm.html#AutomorphicForm.isAutomorphicFnAt_finsum_integral_indicator_canonicalTruncationDomain) and [`AutomorphicForm.setIntegral_finsum_integral_centralScalar_mul_eq_convOp_finsum_integral_indicator_of_hasCompactSupport`](thm.html#AutomorphicForm.setIntegral_finsum_integral_centralScalar_mul_eq_convOp_finsum_integral_indicator_of_hasCompactSupport).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_forall_mem_of_inv_mul_globalPoints_mul_centralScalar_mul_mem_of_isCompact.lean

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

theorem AutomorphicForm.exists_isCompact_forall_mem_of_inv_mul_globalPoints_mul_centralScalar_mul_mem_of_isCompact
    (K : Type) [Field K] [NumberField K]
    (C Cx Cy : Set (AdelicGL2 (𝓞 K) K)) (hC : IsCompact C) (hCx : IsCompact Cx) (hCy : IsCompact Cy)
    (γ : GL (Fin 2) K) :
    ∃ S : Set (AdeleRing (𝓞 K) K)ˣ, IsCompact S ∧
      ∀ z : (AdeleRing (𝓞 K) K)ˣ, (∃ x ∈ Cx, ∃ y ∈ Cy,
          x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ *
            (AutomorphicForm.centralScalar (𝓞 K) K z * y) ∈ C) → z ∈ S := by sorry
