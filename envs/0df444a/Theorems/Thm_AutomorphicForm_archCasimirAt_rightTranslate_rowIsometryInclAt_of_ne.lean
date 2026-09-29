-- Prove2me | Theorems.Thm_AutomorphicForm_archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne
-- name    : AutomorphicForm.archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/41c27af0-099d-5e0f-8326-87f79b153c6e
-- title:
--   Casimir at a real place commutes with translations at other places
-- statement:
--   Let $K$ be a number field, $w$ an infinite place of $K$ with $w$ real, and $x\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ a function on the adelic group $\mathrm{GL}_2$ of $K$ (matrices over the adele ring of $\mathcal{O}_K$ in $K$). Assume: $x$ is continuous; $x$ satisfies `IsArchSmoothAt hw`, i.e. for every $g$ the map $e\mapsto x(g\cdot \mathrm{archRealLiftAt}\,e)$, sending a real $2\times 2$ entry matrix $e$ to the element placed at $w$ with those entries, is $C^\infty$ on $\{e : \det e\neq 0\}$; for each $d$ among the three directions $H,E,F$ the function $\mathrm{archDerivAt}\,d\,x$, namely $g\mapsto \frac{d}{dt}x(g\cdot \mathrm{archFlowAt}\,d\,t)|_{t=0}$, is continuous; and all second derivatives $\mathrm{archDerivAt}\,d\,(\mathrm{archDerivAt}\,d'\,x)$ are continuous. Then for every infinite place $w'\neq w$ and every $k$ in the subgroup `rowIsometrySubgroup₀` of $\mathrm{GL}_2(K_{w'})$, the right translate $g\mapsto x(g\cdot \mathrm{rowIsometryInclAt₀}\,w'\,k)$ by the element with $k$ placed at $w'$ again satisfies `IsArchSmoothAt hw`, has continuous first and second $\mathrm{archDerivAt}$-derivatives in all directions, and satisfies $\Omega_w(R_kx)=R_k(\Omega_wx)$, where $\Omega_w\varphi=-\bigl(\tfrac14 D_HD_H\varphi-\tfrac12 D_H\varphi+D_ED_F\varphi\bigr)$.
--
--   This is the function-level form of the statement that the Casimir operator attached to a real place $w$ commutes with right translation by the isometry group placed at any other infinite place, together with the preservation of the attendant smoothness and continuity conditions. It is one of the stability properties used to show that an eigenspace of the Casimir at $w$ is stable under the relevant translations and convolutions, and it feeds the statements about Casimir eigenvectors and factorizable test functions that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x) (hxs : IsArchSmoothAt hw x)
    (hD1 : ∀ d : ArchDir, Continuous (archDerivAt hw d x))
    (hD2 : ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' x))) :
    ∀ (w' : InfinitePlace K) (hw' : w' ≠ w) (k : rowIsometrySubgroup₀ w'.Completion),
        IsArchSmoothAt hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) ∧
        (∀ d : ArchDir, Continuous (archDerivAt hw d (rightTranslate K (rowIsometryInclAt₀ K w' k) x))) ∧
        (∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d'
          (rightTranslate K (rowIsometryInclAt₀ K w' k) x)))) ∧
        archCasimirAt hw (rightTranslate K (rowIsometryInclAt₀ K w' k) x) =
          rightTranslate K (rowIsometryInclAt₀ K w' k) (archCasimirAt hw x) := by sorry
