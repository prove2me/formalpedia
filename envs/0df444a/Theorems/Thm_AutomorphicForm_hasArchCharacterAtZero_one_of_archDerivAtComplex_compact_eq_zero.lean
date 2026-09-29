-- Prove2me | Theorems.Thm_AutomorphicForm_hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero
-- name    : AutomorphicForm.hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/daccf604-9dd4-5fed-bd52-ff23268df271
-- title:
--   Vanishing of the three compact derivatives forces trivial character at a complex place
-- statement:
--   Let $F$ be a number field and $w$ an infinite place of $F$ with $w$ complex (hypothesis `hw`). Let $Y$ be a finite-dimensional complex subspace of the space of functions $\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ (with $\mathbb{A}_F$ the adele ring of $\mathcal{O}_F$ in $F$), subject to two hypotheses: every $y \in Y$ satisfies `IsArchSmoothAtComplex hw y`, i.e. for each $g$ the function $e \mapsto y(g \cdot \mathrm{archComplexLiftAt}\,hw\,e)$ is $C^\infty$ in the real sense on the set of $2 \times 2$ complex matrices $e$ of nonzero determinant, where $\mathrm{archComplexLiftAt}$ places the invertible matrix $e$ at $w$; and $Y$ is stable under right translation by the subgroup `rowIsometrySubgroup₀ w.Completion` placed at $w$ through `rowIsometryInclAt₀`, in the sense that $g \mapsto y(g \cdot \mathrm{rowIsometryInclAt₀}\,F\,w\,k)$ lies in $Y$ for all such $k$ and all $y \in Y$. Let $x \in Y$ be killed by the three operators $D_{iH}$, $D_{\mathrm{Fm}} - D_E$ and $D_{iE} + D_{i\mathrm{Fm}}$, where $D_d x$ denotes `archDerivAtComplex hw d x`, the function $g \mapsto \frac{d}{dt}\big|_{t=0} x(g \cdot \mathrm{archFlowAtComplex}\,hw\,d\,t)$ along the one-parameter flow in direction $d$ placed at $w$. Then `HasArchCharacterAt₀ F w 1 x` holds: $x$ has the trivial character $1$ at $w$ for the group `rowIsometrySubgroup₀ w.Completion`, the unsubscripted analogue `HasArchCharacterAt` reading $\varphi(g \cdot k) = \chi(k)\varphi(g)$ for all $k$ and $g$.
--
--   This is the finite-dimensional integration step of standard Lie theory at a complex place: annihilation of a vector by the Lie algebra of the compact group $\mathrm{SU}(2)$ sitting inside $\mathrm{GL}_2(F_w)$ forces invariance under the group itself, the trivial-weight case of the analysis of $K_w^1$-types. It is used in the decomposition of cuspidal constituents at a complex place into $\mathrm{SU}(2)$-strings with highest weight vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm

theorem AutomorphicForm.hasArchCharacterAtZero_one_of_archDerivAtComplex_compact_eq_zero
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ Y]
    (hYs : ∀ y ∈ Y, IsArchSmoothAtComplex hw y)
    (hYK : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ y ∈ Y, (fun g => y (g * rowIsometryInclAt₀ F w k)) ∈ Y)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ Y)
    (h0 : archDerivAtComplex hw .iH x = 0)
    (h1 : archDerivAtComplex hw .Fm x - archDerivAtComplex hw .E x = 0)
    (h2 : archDerivAtComplex hw .iE x + archDerivAtComplex hw .iFm x = 0) :
    HasArchCharacterAt₀ F w 1 x := by sorry
