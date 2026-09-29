-- Prove2me | Theorems.Thm_AutomorphicForm_exists_coversModCentre_centreCutSiegelSetAmple
-- name    : AutomorphicForm.exists_coversModCentre_centreCutSiegelSetAmple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/e99cef47-1c90-580d-9413-9a06df1ed72e
-- title:
--   Ample centre-cut Siegel windows still cover modulo centre
-- statement:
--   Let $F$ be a number field. The assertion is the existence of two real constants $\kappa$ and $R$ with $1 \le \kappa$ and $0 \le R$, depending only on $F$, with the following property: for all real numbers $c, u, d_1, d_2$ and every finite set $T$ of elements of $\mathrm{GL}_2$ over the adele ring of $F$, if the union over $x \in T$ of the right translates by $x$ of `centreCutSiegelSet F c u d₁ d₂` satisfies `CoversModCentre F`, then so does the union over $x \in T$ of the right translates by $x$ of `centreCutSiegelSetAmple F c (max u R) d₁ d₂ κ`. Here `centreCutSiegelSet F c u d₁ d₂` consists of those adelic $g$ whose finite component lies in the full level-zero subgroup `finiteIntegralGL2` and whose archimedean component satisfies, at every infinite place $w$ of $F$, the height floor $c \le \mathrm{localHeight}$, the window bound $\mathrm{xWindowSq} \le u^2$, and the determinant condition $\mathrm{archDetNorm}_w(g) \in [d_1, d_2]$, where for a matrix over a normed field $\mathrm{localHeight} = \lVert \det \rVert / \mathrm{rowNormSq}$ and $\mathrm{xWindowSq} = \mathrm{topNormSq}/\mathrm{rowNormSq} - \mathrm{localHeight}^2$; the ample variant imposes in addition the balancing condition $\mathrm{localHeight}_w \le \kappa \cdot \mathrm{localHeight}_{w'}$ for all pairs of infinite places $w, w'$. Finally, `CoversModCentre F D` means that every adelic $g$ admits $\gamma \in \mathrm{GL}_2(F)$ and a unit idele $z$ with $\gamma g \cdot z \in D$, the embeddings being `globalPoints` and the central scalar map `centralScalar`. Note that the floor $c$ and the determinant window $[d_1, d_2]$ are unchanged, only the $x$-window being widened from $u$ to $\max(u, R)$.
--
--   This is the reduction-theoretic step that upgrades a covering by centre-cut Siegel windows to a covering by the ample ones, in which the local heights at the various infinite places are comparable up to a factor $\kappa$; the price is a widening of the $x$-window to a fixed radius $R$ depending only on $F$. It is used in the passage from coverings to statements about cuspidal constituents and about the simultaneous realisation and approximation of automorphic data on ample windows.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_coversModCentre_centreCutSiegelSetAmple.lean

import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import Definitions.Def_AutomorphicForm_SiegelCovering

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.exists_coversModCentre_centreCutSiegelSetAmple
    (F : Type) [Field F] [NumberField F] :
    ∃ κ R : ℝ, 1 ≤ κ ∧ 0 ≤ R ∧
      ∀ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)),
        CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) →
        CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c (max u R) d₁ d₂ κ) := by sorry
