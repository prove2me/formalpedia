-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_nVarpi_eq_of_mem_etaPiece_zero_of_toLieQuot_eq_of_critical_one
-- name    : CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_zero_of_toLieQuot_eq_of_critical_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/cd77edac-8b2b-58b3-905e-748f83570714
-- title:
--   Pi-preimage in η₁(L) at a 1-critical point
-- statement:
--   Let $p$ be prime, let $B$ be a commutative ring of characteristic $p$, let $j\colon W(\mathbb F_{p^2})\to B$ be a ring homomorphism, and let $X$ be a formal $\mathcal O_D$-module over $B$: a $2$-dimensional commutative formal group law $X.F$ together with an action of $W(\mathbb F_{p^2})$ by law endomorphisms and a law endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ[a] = [\sigma a]\circ\varpi$. Write $M$ for the Cartier module $\mathtt{CartierModule}\ p\ X.F$ and, for $n$, let $M_n$ be the subgroup of $f\in M$ with $[\,\omega(c)\,]_*f = j(\omega(c))^{p^n}\cdot f$ for every $c\in\mathbb F_{p^2}$, $\omega$ the Teichmüller lift. Assume $M_0$ and $M_1$ are complementary ($hc$), and let $D$ be the resulting graded Cartier module data on $M$, with Verschiebung $V$, Frobenius, $\Pi$ induced by $\varpi$, and the two pieces $M_0, M_1$. Let $L\colon M\to N(M)$ be an additive map which is a canonical $L$-map (a Cartier $L$-map admitting a lift along a surjection from a $p$-torsion-free ring carrying a special Cartier module). Assume: index $1$ is critical, i.e. for every $m\in M_1$ there is $g\in M$ with $Vg = \Pi m$; and $L$ is explicit on $M_1$, i.e. $L x = [(y,0)]$ whenever $x\in M_1$ and $Vy = \Pi x$. Let $z\in N(M)$ lie in $\eta_0(L)$, the intersection of $\eta(L)$ with the degree-$0$ piece of $N(M)$, and suppose its tangent class $\mathrm{toLieQuot}(z)$ equals the class of $\Pi m_1$ in $M/VM$ for some $m_1\in M_1$. Then there exists $z_1\in\eta_1(L)$ with $\Pi_N(z_1) = z$, where $\Pi_N$ is the map induced by $\Pi$ on $N(M)$.
--
--   This is the realisation, in the even piece at a point where the index $1$ is critical, of Drinfeld's condition [C2] on the quadruples classifying special formal modules, in the form given by Boutot and Carayol: a fixed point of $\varphi_L$ in degree $0$ whose tangent class lies in the image of $\Pi M_1$ is $\Pi$ of a fixed point in degree $1$. It is the index-swapped counterpart of the corresponding statement for the odd piece, and is used in deducing the version over algebraically closed base, [`CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_of_toLieQuot_eq_of_isAlgClosed`](thm.html#CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_of_toLieQuot_eq_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_nVarpi_eq_of_mem_etaPiece_zero_of_toLieQuot_eq_of_critical_one.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_zero_of_toLieQuot_eq_of_critical_one
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B)
    (X : FormalODModule p B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (h1 : ∀ m ∈ X.gradedPiece j 1, ∃ g : MvFormalGroup.CartierModule p X.F, MvFormalGroup.CartierModule.verschiebungInt g = MvFormalGroup.CartierModule.endAct X.varpiEnd m)
    (hL1 : ∀ x y : MvFormalGroup.CartierModule p X.F, x ∈ X.gradedPiece j 1 →
      MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct X.varpiEnd x → L x = (X.toGradedCartierModuleData j hc).nMk (y, 0))
    (z : (X.toGradedCartierModuleData j hc).NMod) (hz : z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 0)
    (htan : ∃ m₁ ∈ X.gradedPiece j 1, (X.toGradedCartierModuleData j hc).toLieQuot z = (X.toGradedCartierModuleData j hc).vRange.mkQ (MvFormalGroup.CartierModule.endAct X.varpiEnd m₁)) :
    ∃ z₁ ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 1, (X.toGradedCartierModuleData j hc).nVarpi z₁ = z := by sorry
