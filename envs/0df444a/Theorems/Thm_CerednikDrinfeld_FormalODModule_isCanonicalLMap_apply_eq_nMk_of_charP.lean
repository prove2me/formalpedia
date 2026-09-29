-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_charP
-- name    : CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/07d66f39-f146-518b-8f9b-35a8146dab39
-- title:
--   Canonical L-maps on critical graded pieces in characteristic p
-- statement:
--   Let $p$ be a prime, let $B$ be a commutative ring with $\mathrm{char}\,B=p$, let $j\colon W(\mathbb F_{p^2})\to B$ be a ring homomorphism, and let $X$ be a formal $\mathcal O_D$-module over $B$: a $2$-dimensional commutative formal group law $F$ over $B$ together with law endomorphisms $\mathrm{act}(a)$ for $a\in W(\mathbb F_{p^2})$, additive and multiplicative in $a$ with $\mathrm{act}(1)=\mathrm{id}$, and a law endomorphism $\varpi$ satisfying $\varpi\circ\varpi=\mathrm{act}(p)$ and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\sigma a)\circ\varpi$. Write $M$ for the Cartier module of $F$; for $n\in\mathbb N$ the graded piece $M_n$ is the subgroup of those $f$ with $\mathrm{act}(\tau(c))_*f=j(\tau(c))^{p^n}\cdot f$ for every $c\in\mathbb F_{p^2}$, $\tau$ the Teichmüller lift. Assume $M_0$ and $M_1$ are complementary, so that $M$ with Frobenius, the integral Verschiebung, the action of $\varpi$ and the two pieces forms graded Cartier module data $D$. Let $L\colon M\to N(M)$ be an additive map which is a canonical $L$-map, i.e. a Cartier $L$-map for $D$ admitting a lift along a surjection $\varphi\colon S\to B$ from a ring without $p$-torsion, through special graded Cartier module data $Dl$ over $S$ with a base-change map $Dl.M\to M$ and a Cartier $L$-map upstairs compatible with $L$. Let $i\in\mathbb N$ be such that every $m\in M_i$ satisfies $\varpi_*m\in V M$. Then for $x\in M_i$ and $y\in M$ with $V y=\varpi_*x$ one has $L x = ((y,0))$, the class of $(y,0)$ under the map $\mathrm{nMk}$ into $N(M)$.
--
--   This is the characteristic-$p$ form of the computation of the canonical $L$-map on a critical graded piece of the Cartier module of a formal $\mathcal O_D$-module, as in Boutot–Carayol's treatment of Drinfeld's $p$-adic uniformisation; stating it over an arbitrary base of characteristic $p$ makes it applicable to geometric fibres and not only to a base point. It is the input to the subsequent identifications of classes in $N(M)$ and of graded pieces used in verifying Drinfeld's conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_apply_eq_nMk_of_charP.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.FormalODModule.isCanonicalLMap_apply_eq_nMk_of_charP
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B)
    (X : FormalODModule p B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (i : ℕ) (hi : ∀ m ∈ X.gradedPiece j i, ∃ g : MvFormalGroup.CartierModule p X.F, MvFormalGroup.CartierModule.verschiebungInt g = MvFormalGroup.CartierModule.endAct X.varpiEnd m)
    (x y : MvFormalGroup.CartierModule p X.F) (hx : x ∈ X.gradedPiece j i) (hy : MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct X.varpiEnd x) :
    L x = (X.toGradedCartierModuleData j hc).nMk (y, 0) := by sorry
