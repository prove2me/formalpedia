-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_tangent_eq_of_mkQ_eq
-- name    : CerednikDrinfeld.FormalODModule.tangent_eq_of_mkQ_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/316a0476-3350-5ba7-968f-afa3cf3d3ae0
-- title:
--   Classes modulo VM have equal tangent vectors
-- statement:
--   Let $p$ be a prime, $B$ a commutative ring, and $j \colon \mathbb{W}(\mathbb{F}_{p^2}) \to B$ a ring homomorphism, where [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17) is the Witt vector ring of the field `GaloisField p 2`. Let $X$ be a formal $\mathcal{O}_D$-module over $B$, that is: a $2$-dimensional formal group law $F$ over $B$ together with a commutativity witness, a family of endomorphism laws `act a` indexed by $a \in \mathbb{W}(\mathbb{F}_{p^2})$ which is additive, multiplicative and unital for substitution, and a law $\varpi$ with $\varpi \circ \varpi = \mathrm{act}(p)$ and $\varpi \circ \mathrm{act}(a) = \mathrm{act}(\sigma a) \circ \varpi$. Let $hc$ assert that the two additive subgroups `X.gradedPiece j 0` and `X.gradedPiece j 1` of the Cartier module `CartierModule p X.F` are complements of one another; these consist of those $f$ with $\mathrm{endAct}(X.\mathrm{actEnd}(\tau(c)))\,f = \mathrm{homothety}(j(\tau(c))^{p^{n}})\,f$ for all $c \in \mathbb{F}_{p^2}$, with $\tau$ the Teichmüller lift and $n = 0$, $1$. Let $m, m'$ be elements of `CartierModule p X.F`, that is, $2$-tuples of multivariate power series in variables indexed by $\mathbb{N}$ with zero constant term satisfying the Cartier additivity identity for $F$. If $m$ and $m'$ have the same image under the quotient map of `CartierModule p X.F` by the $\mathbb{W}(B)$-submodule `vRange` of the graded Cartier module data attached to $X$, $j$, $hc$ — the image of the integral Verschiebung `verschiebungInt` — then $m$ and $m'$ have the same tangent vector, where the tangent map sends $f$ to the tuple of coefficients of the first variable in each component of $f$, an element of $B^{2}$.
--
--   This records that the tangent map on the Cartier module of a formal $\mathcal{O}_D$-module factors through the quotient by the image of Verschiebung, so that tangent vectors are well defined on $M/VM$. It is used in the comparison of Cartier quadruples with lines in $M/VM$ and in the base-change behaviour of the associated rigidification data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_tangent_eq_of_mkQ_eq.lean

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
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.tangent_eq_of_mkQ_eq
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (X : CerednikDrinfeld.FormalODModule p B) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (m m' : MvFormalGroup.CartierModule p X.F)
    (h : (X.toGradedCartierModuleData j hc).vRange.mkQ m = (X.toGradedCartierModuleData j hc).vRange.mkQ m') :
    MvFormalGroup.CartierModule.tangent m = MvFormalGroup.CartierModule.tangent m' := by sorry
