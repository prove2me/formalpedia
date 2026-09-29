-- Prove2me | Theorems.Thm_AutomorphicForm_isFactorizableTestFn_conj_comp_inv
-- name    : AutomorphicForm.isFactorizableTestFn_conj_comp_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/c6e6486e-d26d-5f4c-a4f5-42dd93586db5
-- title:
--   Factorizable test functions are stable under f↦̄f(·⁻¹)
-- statement:
--   Let $K$ be a number field and let $f$ be a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_K)$, where $\mathbb{A}_K$ is the adele ring of $K$ (formed from $\mathcal{O}_K$ and $K$) and $\mathrm{GL}_2$ denotes the general linear group of $2\times 2$ invertible matrices over it. Assume $f$ is a factorizable test function in the sense of the project predicate `IsFactorizableTestFn`: there are functions $f_\infty$ on $\mathrm{GL}_2$ of the infinite adele ring of $K$ and $f_{\mathrm{fin}}$ on $\mathrm{GL}_2$ of the finite adele ring of $\mathcal{O}_K$ in $K$ such that $f_\infty$ is of the form $f_\infty(g)=\Phi(\mathrm{archEntries}\,g)$ for some $C^\infty$ function $\Phi$ on matrix entries valued in the mixed space of $K$ and has compact support, $f_{\mathrm{fin}}$ is locally constant with compact support, and $f(g)=f_\infty(\mathrm{glArch}\,g)\cdot f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ for every $g$, the two maps $\mathrm{glArch}$ and $\mathrm{glFin}$ being the group homomorphisms induced on $\mathrm{GL}_2$ by the archimedean and finite projections of the adeles. The conclusion is that the function $y\mapsto\overline{f(y^{-1})}$ again satisfies `IsFactorizableTestFn` for $K$.
--
--   This is the closure of the class of pure-tensor test functions on $\mathrm{GL}_2(\mathbb{A}_K)$ under passage to the adjoint $f^*(y)=\overline{f(y^{-1})}$, the operation for which right convolution by $f^*$ is adjoint to right convolution by $f$. It is used in the computation of an integral of a product against a right convolution in terms of inner products with respect to an orthonormal family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isFactorizableTestFn_conj_comp_inv.lean

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

theorem AutomorphicForm.isFactorizableTestFn_conj_comp_inv
    (K : Type) [Field K] [NumberField K]
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : IsFactorizableTestFn K f) :
    IsFactorizableTestFn K (fun y : AdelicGL2 (𝓞 K) K => conj (f y⁻¹)) := by sorry
