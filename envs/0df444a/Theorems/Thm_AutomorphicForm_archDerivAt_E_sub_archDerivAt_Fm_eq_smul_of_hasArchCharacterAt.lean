-- Prove2me | Theorems.Thm_AutomorphicForm_archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt
-- name    : AutomorphicForm.archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/853e2c72-b825-5844-bd51-0b0b06db5407
-- title:
--   Infinitesimal weight in along the rotation direction E-F
-- statement:
--   Let $K$ be a number field, $w$ an infinite place of $K$ with `hw : w.IsReal` a witness that $w$ is real, and $n$ an integer. Let $y \colon \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be a complex-valued function on the adelic group `AdelicGL2 (𝓞 K) K`, the general linear group of rank $2$ over the adele ring of $K$. Assume two things. First, `IsArchSmoothAt hw y`: for every $g$ in the adelic group, the function sending a real $2 \times 2$ matrix $e$ to $y(g \cdot \mathrm{archRealLiftAt}\,hw\,e)$, where `archRealLiftAt` places an invertible real matrix into the $\mathrm{GL}_2$ factor at $w$ (and sends singular matrices to $1$), is $C^\infty$ in the real sense on the open set of matrices with nonzero determinant. Second, `HasArchCharacterAt₀ K w (archWeightCharAt hw n) y`: the function $y$ transforms under right translation by the elements of the group `rowIsometrySubgroup₀ w.Completion`, embedded at the place $w$, by the character `archWeightCharAt hw n`, the $n$-th power of the character `archWeightOneAt hw` obtained by transporting `archWeightOneℝ` along the norm-preserving identification of $K_w$ with $\mathbb{R}$. The conclusion is an identity of functions on the adelic group: $$\mathrm{archDerivAt}\,hw\,\mathsf{E}\,y - \mathrm{archDerivAt}\,hw\,\mathsf{Fm}\,y = (i n) \cdot y,$$ where for a direction $d$ among the three constructors `H`, `E`, `Fm` of `ArchDir`, $(\mathrm{archDerivAt}\,hw\,d\,y)(g)$ is the derivative at $t = 0$ of $t \mapsto y(g \cdot \mathrm{archFlowAt}\,hw\,d\,t)$, the flow `archFlowAt` being the one-parameter family `archFlowMatrix d t` inserted into the $\mathrm{GL}_2$ factor at $w$.
--
--   This is the infinitesimal form, at a real place, of the weight condition on an automorphic form: a function of weight $n$ for the rotation subgroup at $w$ is an eigenfunction with eigenvalue $in$ of the Lie derivative along the rotation direction $E - \mathsf{Fm}$. It is used in the analysis of cuspidal constituents, where it feeds the computation of the Casimir eigenvalue and the resulting dichotomy between principal-series, discrete-series and trivial behaviour at the archimedean places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (n : ℤ)
    (y : AdelicGL2 (𝓞 K) K → ℂ) (hys : IsArchSmoothAt hw y)
    (hyn : HasArchCharacterAt₀ K w (archWeightCharAt hw n) y) :
    archDerivAt hw .E y - archDerivAt hw .Fm y = (Complex.I * n) • y := by sorry
