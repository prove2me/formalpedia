-- Prove2me | Theorems.Thm_AutomorphicForm_archDerivAt_commutator_of_isArchSmoothAt
-- name    : AutomorphicForm.archDerivAt_commutator_of_isArchSmoothAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/96e7fa24-6018-5a07-8947-adfd4f22bca5
-- title:
--   mathfraksl₂ commutation relations for right-flow derivatives at a real place
-- statement:
--   Let $F$ be a number field, $w$ an infinite place of $F$ together with a proof $hw$ that $w$ is real, and $\varphi$ a complex-valued function on the adelic group $\mathrm{GL}_2(\mathbb{A}_{F})$, i.e. on `AdelicGL2 (𝓞 F) F`, the general linear group of $2\times 2$ matrices over the adele ring of $F$. Assume `IsArchSmoothAt hw φ`: for every $g$ in that group, the function $e \mapsto \varphi(g \cdot \mathrm{archRealLiftAt}\ hw\ e)$ of a real $2\times2$ matrix $e$ is $C^{\infty}$ on the set of $e$ with $\det e \neq 0$, where `archRealLiftAt` sends an invertible real matrix to the corresponding adelic element placed at the real place $w$ (and to $1$ when the determinant vanishes). For a direction $d$ among the three constructors `H`, `E`, `Fm` of `ArchDir`, the operator $\mathrm{archDerivAt}\ hw\ d$ sends $\varphi$ to the function $g \mapsto \frac{d}{dt}\varphi\bigl(g\cdot \mathrm{archFlowAt}\ hw\ d\ t\bigr)\big|_{t=0}$, the flow $\mathrm{archFlowAt}\ hw\ d\ t$ being the matrix `archFlowMatrix d t` placed at $w$. The conclusion is the conjunction of three identities of functions: $D_H D_E \varphi - D_E D_H \varphi = 2\,D_E\varphi$, $D_H D_{Fm}\varphi - D_{Fm} D_H \varphi = -2\,D_{Fm}\varphi$, and $D_E D_{Fm}\varphi - D_{Fm} D_E \varphi = D_H \varphi$, with scalars acting by pointwise multiplication in $\mathbb{C}$.
--
--   These are the commutation relations $[H,E]=2E$, $[H,F]=-2F$, $[E,F]=H$ of $\mathfrak{sl}_2(\mathbb{R})$, realised for the action by left-invariant differentiation along right flows at a single real place of $F$ on functions smooth there. They underlie the manipulation of the Casimir operator through raising and lowering operators and the weight-shift arguments, and are cited by [`AutomorphicForm.archCasimirAt_eq_raising_lowering_of_isArchSmoothAt`](thm.html#AutomorphicForm.archCasimirAt_eq_raising_lowering_of_isArchSmoothAt), [`AutomorphicForm.archCasimirAt_foldr_archDeriv_eq_foldr_archDeriv_archCasimirAt`](thm.html#AutomorphicForm.archCasimirAt_foldr_archDeriv_eq_foldr_archDeriv_archCasimirAt) and [`AutomorphicForm.isArchLowestWeightAt_iff_and_isArchHolomorphicAt_iff_lower_eq_zero_of_hasArchCharacterAt`](thm.html#AutomorphicForm.isArchLowestWeightAt_iff_and_isArchHolomorphicAt_iff_lower_eq_zero_of_hasArchCharacterAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archDerivAt_commutator_of_isArchSmoothAt.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.archDerivAt_commutator_of_isArchSmoothAt
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAt hw φ) :
    archDerivAt hw .H (archDerivAt hw .E φ) - archDerivAt hw .E (archDerivAt hw .H φ) = (2 : ℂ) • archDerivAt hw .E φ ∧
    archDerivAt hw .H (archDerivAt hw .Fm φ) - archDerivAt hw .Fm (archDerivAt hw .H φ) = (-2 : ℂ) • archDerivAt hw .Fm φ ∧
    archDerivAt hw .E (archDerivAt hw .Fm φ) - archDerivAt hw .Fm (archDerivAt hw .E φ) = archDerivAt hw .H φ := by sorry
