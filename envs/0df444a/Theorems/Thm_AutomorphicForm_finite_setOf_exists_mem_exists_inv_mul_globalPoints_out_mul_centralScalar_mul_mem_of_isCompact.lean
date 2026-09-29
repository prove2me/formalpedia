-- Prove2me | Theorems.Thm_AutomorphicForm_finite_setOf_exists_mem_exists_inv_mul_globalPoints_out_mul_centralScalar_mul_mem_of_isCompact
-- name    : AutomorphicForm.finite_setOf_exists_mem_exists_inv_mul_globalPoints_out_mul_centralScalar_mul_mem_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/9eefd8cc-687a-5dd1-8bb2-d9da9c411faf
-- title:
--   Finiteness of rational classes mod centre meeting a compact set
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal{O}_K$ and adele ring $\mathbb{A}_K$, and write $\mathrm{GL}_2(\mathbb{A}_K)$ for the general linear group of $2\times 2$ matrices over $\mathbb{A}_K$. Let $C$, $C_x$, $C_y$ be three compact subsets of $\mathrm{GL}_2(\mathbb{A}_K)$. Consider the quotient $\mathrm{GL}_2(K)/Z$ of the rational group by its centre, and for a class $q$ let $q.\mathrm{out}$ denote the chosen representative in $\mathrm{GL}_2(K)$ supplied by `Quotient.out`; write $\mathrm{globalPoints}$ for the homomorphism $\mathrm{GL}_2(K)\to\mathrm{GL}_2(\mathbb{A}_K)$ obtained by applying the structure map $K\to\mathbb{A}_K$ entrywise, and $\mathrm{centralScalar}(z)$ for the scalar matrix $z\cdot 1_2$ attached to an idele $z\in\mathbb{A}_K^\times$. The assertion is that the set of those classes $q\in \mathrm{GL}_2(K)/Z$ for which there exist $x\in C_x$, $y\in C_y$ and $z\in\mathbb{A}_K^\times$ with
--   $$x^{-1}\,\mathrm{globalPoints}(q.\mathrm{out})\,\bigl(z\cdot 1_2\bigr)\,y\ \in\ C$$
--   is finite.
--
--   This is the finiteness statement underlying the discreteness of $\mathrm{GL}_2(K)$ in $\mathrm{GL}_2(\mathbb{A}_K)$, in the form needed after the centre has been integrated out: only finitely many classes modulo the centre contribute, uniformly for the two translating variables in compact sets. It makes the centre-folded kernel $\sum_{\gamma\in \mathrm{GL}_2(K)/Z}\int_{\mathbb{A}_K^\times}\xi(z)f(x^{-1}\gamma z y)\,dz$ of a compactly supported $f$ a locally finite sum, and is used in establishing continuity and the automorphy properties of such kernel sums.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finite_setOf_exists_mem_exists_inv_mul_globalPoints_out_mul_centralScalar_mul_mem_of_isCompact.lean

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

theorem AutomorphicForm.finite_setOf_exists_mem_exists_inv_mul_globalPoints_out_mul_centralScalar_mul_mem_of_isCompact
    (K : Type) [Field K] [NumberField K]
    (C Cx Cy : Set (AdelicGL2 (𝓞 K) K)) (hC : IsCompact C) (hCx : IsCompact Cx) (hCy : IsCompact Cy) :
    {q : GL (Fin 2) K ⧸ Subgroup.center (GL (Fin 2) K) |
        ∃ x ∈ Cx, ∃ y ∈ Cy, ∃ z : (AdeleRing (𝓞 K) K)ˣ,
          x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K q.out *
            (AutomorphicForm.centralScalar (𝓞 K) K z * y) ∈ C}.Finite := by sorry
