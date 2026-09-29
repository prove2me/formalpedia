-- Prove2me | Theorems.Thm_AutomorphicForm_archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one
-- name    : AutomorphicForm.archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/f347f096-9195-53b4-a102-74ef834d46f3
-- title:
--   Compact-direction derivatives vanish for trivial character at a complex place
-- statement:
--   Let $F$ be a number field, $w$ an infinite place of $F$ with $w$ complex (witnessed by `hw : w.IsComplex`), and let $\varphi$ be a complex-valued function on the adelic group $\mathrm{GL}_2(\mathbb{A}_{F})$, i.e. on `AdelicGL2 (𝓞 F) F`, the general linear group of $2\times 2$ matrices over the adele ring of $F$. Assume first that $\varphi$ is smooth at $w$ in the sense of `IsArchSmoothAtComplex hw`: for every adelic $g$, the function sending a matrix $e \colon \mathrm{Fin}\ 2 \to \mathrm{Fin}\ 2 \to \mathbb{C}$ to $\varphi\bigl(g \cdot \text{archComplexLiftAt } hw\, e\bigr)$, where the lift embeds an invertible $e$ into the adelic group at the place $w$ (and is $1$ on singular $e$), is $C^\infty$ over $\mathbb{R}$ on the open set $\{e \mid \det e \neq 0\}$. Assume second the predicate `HasArchCharacterAt₀ F w 1 φ`, expressing that $\varphi$ has trivial archimedean character at $w$, the character argument being $1$ (compare `HasArchCharacterAt`, which for a character $\chi$ of the row-isometry subgroup of $\mathrm{GL}_2(F_w)$ requires $\varphi(g\,k) = \chi(k)\varphi(g)$ for all such $k$ and all $g$). Then, writing $D_d\varphi =$ `archDerivAtComplex hw d φ` for the function $g \mapsto \frac{d}{dt}\varphi\bigl(g\cdot \text{archFlowAtComplex } hw\, d\, t\bigr)\big|_{t=0}$ attached to a direction $d$ among the six constructors $H, E, F^{-}, iH, iE, iF^{-}$ of `ArchDirComplex`, one has the three identities of functions on the adelic group: $D_{iH}\varphi = 0$, $D_{F^{-}}\varphi = D_{E}\varphi$ and $D_{iF^{-}}\varphi = -D_{iE}\varphi$.
--
--   This is the infinitesimal form of invariance under the compact row-isometry group at a complex place: the three flow directions tangent to that group annihilate a function with trivial archimedean character there, leaving only the symmetric combinations. It feeds the analysis of the Casimir operator on cuspidal constituents at a complex place, being used in [`AutomorphicForm.CuspidalConstituent.casimirBar_eq_conj_and_sl2Invariant_of_casimir_eq_zero_of_isCuspConstituent_of_isComplex`](thm.html#AutomorphicForm.CuspidalConstituent.casimirBar_eq_conj_and_sl2Invariant_of_casimir_eq_zero_of_isCuspConstituent_of_isComplex) and in [`AutomorphicForm.CuspidalConstituent.neg_le_casimir_re_of_highestWeight_of_isCuspConstituent_of_isComplex`](thm.html#AutomorphicForm.CuspidalConstituent.neg_le_casimir_re_of_highestWeight_of_isCuspConstituent_of_isComplex).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_ArchWeightChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ)
    (hχ : HasArchCharacterAt₀ F w 1 φ) :
    archDerivAtComplex hw .iH φ = 0 ∧
    archDerivAtComplex hw .Fm φ = archDerivAtComplex hw .E φ ∧
    archDerivAtComplex hw .iFm φ = -archDerivAtComplex hw .iE φ := by sorry
