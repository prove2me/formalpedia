-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_free_lieZero_map_and_free_lieOne_map_of_isSpecial
-- name    : CerednikDrinfeld.FormalODModule.exists_free_lieZero_map_and_free_lieOne_map_of_isSpecial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/507df1b7-ec40-590c-8543-311ca1dd6a61
-- title:
--   Local freeness of the Lie eigenlines of a special formal mathcal O_D-module
-- statement:
--   Let $p$ be a prime, write $\mathbb{Z}_{p^2} := W(\mathbb{F}_{p^2})$ for [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17), let $B$ be a commutative ring, let $j : \mathbb{Z}_{p^2} \to B$ be a ring homomorphism, and let $X$ be a formal $\mathcal O_D$-module over $B$, i.e. a commutative $2$-dimensional formal group law $F$ over $B$ together with an action of $\mathbb{Z}_{p^2}$ by endomorphisms of $F$ and an endomorphism $\varpi$ of $F$ satisfying $\varpi \circ \varpi = [p]$ and $\varpi \circ [a] = [\sigma(a)] \circ \varpi$, $\sigma$ the Frobenius of $\mathbb{Z}_{p^2}$. Inside the Lie module $X.\mathrm{Lie} = B^{2}$ consider the two submodules $\mathrm{lieZero}$, the intersection over $a \in \mathbb{Z}_{p^2}$ of the kernels of $\mathrm{lieAct}(a) - j(a)\cdot\mathrm{id}$, and $\mathrm{lieOne}$, the same with $j(\sigma(a))$ in place of $j(a)$. Assume $X$ is special for $j$: these two submodules are complementary in $X.\mathrm{Lie}$ and each is an invertible $B$-module. Then for every prime $x$ of $B$ there is $f \in B$ with $f \notin x$ such that, for the formal $\mathcal O_D$-module over the localisation $B_f$ obtained by applying $B \to B_f$ to the coefficients of $F$, of the action and of $\varpi$, and for the composite $\mathbb{Z}_{p^2} \to B \to B_f$, both the $\mathrm{lieZero}$ and the $\mathrm{lieOne}$ submodules are free $B_f$-modules.
--
--   This is the existence of local frames for the two Lie eigenline sheaves of a special formal $\mathcal O_D$-module: invertibility gives them locally free rank-one structure only after passing to a basic open neighbourhood, which is what the statement provides. It is used to produce homogeneous bases in the nilpotent case, and thence in the rigidification of the deformation functors occurring in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_free_lieZero_map_and_free_lieOne_map_of_isSpecial.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.exists_free_lieZero_map_and_free_lieOne_map_of_isSpecial
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B]
    (j : CerednikDrinfeld.Zp2 p →+* B) (X : CerednikDrinfeld.FormalODModule p B) (hX : X.IsSpecial j)
    (x : PrimeSpectrum B) :
    ∃ f : B, f ∉ x.asIdeal ∧
      Module.Free (Localization.Away f)
        ↥((X.map (algebraMap B (Localization.Away f))).lieZero ((algebraMap B (Localization.Away f)).comp j)) ∧
      Module.Free (Localization.Away f)
        ↥((X.map (algebraMap B (Localization.Away f))).lieOne ((algebraMap B (Localization.Away f)).comp j)) := by sorry
