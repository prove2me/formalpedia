-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced
-- name    : CerednikDrinfeld.FormalODModule.eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/4677952f-27dc-5dcb-a9d7-ae1ef03e3794
-- title:
--   Injectivity of varpi on Cartier modules over reduced bases
-- statement:
--   Let $p$ be a prime and let $B$ be a reduced commutative ring of characteristic $p$, equipped with a ring homomorphism $j \colon \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to B$. Let $X$ be a formal $\mathcal{O}_D$-module over $B$ in the sense of the structure `FormalODModule`: a two-dimensional commutative formal group law $F$ over $B$, an action of $\mathbb{Z}_{p^2}$ by endomorphisms of $F$ (unital, multiplicative for composition and additive for addition via $F$), and a further endomorphism $\varpi$ of $F$ with $\varpi \circ \varpi$ equal to the action of $p$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$ for all $a$, where $\sigma$ is the Witt-vector Frobenius. Assume $X$ is special for $j$, i.e. the two eigen-submodules of the Lie algebra on which each $a \in \mathbb{Z}_{p^2}$ acts by $j(a)$, respectively by $j(\sigma a)$, are complementary and each invertible as a $B$-module; and assume $X$ has height $4$, i.e. the multiplication-by-$p$ series of $X$ has kernel of degree $p^4$. Let $m$ be an element of the Cartier module of $F$ (a pair of power series in countably many variables with zero constant term satisfying the compatibility of the Witt addition law with $F$) such that the endomorphism of the Cartier module induced by $\varpi$ annihilates $m$. Then $m = 0$.
--
--   This is the torsion-freeness statement for special formal $\mathcal{O}_D$-modules of height $4$ in the Čerednik–Drinfeld uniformisation: $\varpi$ (hence, since $\varpi^2 = p$, also $p$) acts injectively on the Cartier module, over an arbitrary reduced base of characteristic $p$. It is the input to the descriptions of the $\eta$-pieces and of the quotients attached to critical points, and to the later divisibility arguments that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.FormalODModule.eq_zero_of_endAct_varpiEnd_eq_zero_of_isReduced
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] [IsReduced B] (j : Zp2 p →+* B)
    (X : FormalODModule p B) (hX : X.IsSpecial j) (hX4 : X.HasHeight 4)
    (m : MvFormalGroup.CartierModule p X.F) (hm : MvFormalGroup.CartierModule.endAct X.varpiEnd m = 0) :
    m = 0 := by sorry
