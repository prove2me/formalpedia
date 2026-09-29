-- Prove2me | Theorems.Thm_AutomorphicForm_archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAtZero_of_isArchSmoothAt
-- name    : AutomorphicForm.archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAtZero_of_isArchSmoothAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/425313d8-ac5d-555c-93cc-872100d3c436
-- title:
--   Weight-k forms satisfy (E-F)φ = ik φ at a real place
-- statement:
--   Let $F$ be a number field, $w$ a real infinite place of $F$ (with witness $hw : w.\mathrm{IsReal}$), $k$ an integer, and $\varphi$ a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $F$, i.e. on `AdelicGL2 (𝓞 F) F`. Assume two things. First, `IsArchSmoothAt hw φ`: for every adelic $g$, the function sending a real $2\times 2$ matrix $e$ to $\varphi(g\cdot \mathrm{archRealLiftAt}\ hw\ e)$, where `archRealLiftAt` sends an invertible $e$ to its image in the adelic group under the embedding of $\mathrm{GL}_2(\mathbb{R})$ at the place $w$ (and to $1$ otherwise), is $C^\infty$ on the set of $e$ with $\det e \neq 0$. Second, the predicate `HasArchCharacterAt₀` holds for $F$, $w$, $\varphi$ and the character obtained by composing the weight-$k$ character `archWeightCharℝ k` of the real row-isometry subgroup with the transport map `rowIsometrySubgroup₀Map` along the norm-preserving ring isomorphism `ringEquivRealOfIsReal hw` from the completion of $F$ at $w$ to $\mathbb{R}$; this expresses that $\varphi$ transforms by that character under right translation by the relevant rotation subgroup at $w$. The conclusion is an equality of functions on the adelic group: $\mathrm{archDerivAt}\ hw\ \mathrm{ArchDir.E}\ \varphi - \mathrm{archDerivAt}\ hw\ \mathrm{ArchDir.Fm}\ \varphi = (i k)\cdot \varphi$, where `archDerivAt hw d φ` at $g$ is the derivative at $t = 0$ of $t \mapsto \varphi(g \cdot \mathrm{archFlowAt}\ hw\ d\ t)$, the flow at $w$ in the direction $d$ (here the raising direction $E$ and the lowering direction $Fm$).
--
--   This is the infinitesimal form of the $K$-type condition: on a function of weight $k$ at a real place, the element $E - F$ of $\mathfrak{sl}_2$, which generates the rotation subgroup, acts by the scalar $ik$. It is used in the Casimir/raising–lowering estimates for the archimedean cut submodule and in the determination of the archimedean parameters and Whittaker coefficients in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAtZero_of_isArchSmoothAt.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open LanglandsTunnell LanglandsTunnell.RealArchParam
open LanglandsTunnell.Converse

theorem AutomorphicForm.archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAtZero_of_isArchSmoothAt
    {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal) (k : ℤ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hsm : IsArchSmoothAt hw φ)
    (hk : HasArchCharacterAt₀ F w ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ) :
    archDerivAt hw ArchDir.E φ - archDerivAt hw ArchDir.Fm φ = (Complex.I * (k : ℂ)) • φ := by sorry
