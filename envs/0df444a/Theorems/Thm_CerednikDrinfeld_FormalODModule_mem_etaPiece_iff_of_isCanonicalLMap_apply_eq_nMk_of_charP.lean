-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP
-- name    : CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/96f8442c-b67d-5bc1-8d65-f1441f4dd2a7
-- title:
--   The η-piece at a critical index in characteristic p
-- statement:
--   Let $p$ be a prime, $B$ a commutative ring of characteristic $p$, $j\colon W(\mathbb F_{p^2})\to B$ a ring homomorphism and $X$ a formal $\mathcal O_D$-module over $B$, i.e. a two-dimensional commutative formal group law $F$ over $B$ together with an additive action of $W(\mathbb F_{p^2})$ by endomorphisms and an endomorphism $\varpi$ with $\varpi\circ\varpi=[p]$ and $\varpi\circ a=\sigma(a)\circ\varpi$. Write $M=\mathrm{CartierModule}\,p\,X.F$, let $\Pi$ be the operator `endAct X.varpiEnd` induced by $\varpi$, let $V$ be `verschiebungInt`, and let $M_n\subseteq M$ be the $n$-th graded piece, the set of $f$ with $\mathrm{endAct}(X.\mathrm{actEnd}(\tau(c)))f=j(\tau(c))^{p^n}\cdot f$ for every $c\in\mathbb F_{p^2}$, $\tau$ the Teichmüller lift. Assume $h_c$: $M_0$ and $M_1$ are complementary, so that $M$ with $\mathrm{frobenius}$, $V$, $\Pi$ and the two pieces forms the graded Cartier datum $D=X.\mathrm{toGradedCartierModuleData}\,j\,h_c$; let $L\colon M\to D.\mathrm{NMod}$ be an additive map that is a canonical $L$-map (a Cartier $L$-map, in particular $L(Vx)=\mathrm{nMk}(\Pi x,0)$, admitting a lift along a surjection from a $p$-torsion-free ring carrying a special Cartier datum with a base-change comparison). Assume further that $\Pi$ is injective ($\Pi m=0\Rightarrow m=0$), and fix $i\in\{0,1\}$ such that every $m\in M_i$ satisfies $\Pi m\in V(M)$, and such that for $x\in M_i$ and any $y$ with $Vy=\Pi x$ one has $L(x)=\mathrm{nMk}(y,0)$. Then the conclusion has two parts: first, an element $z$ of $D.\mathrm{NMod}$ lies in $D.\mathrm{etaPiece}\,L\,i$, the intersection of $D.\mathrm{eta}\,L$ with the $i$-th piece of $D.\mathrm{NMod}$, if and only if $z=\mathrm{nMk}(m,0)$ for some $m\in M_i$ with $\Pi m=Vm$; second, the map $m\mapsto \mathrm{nMk}(m,0)$ is injective on $M_i$.
--
--   This is the description of the $\eta$-part of the Cartier-theoretic module $N$ in a critical degree, in the form used in the Čerednik–Drinfeld uniformisation following Boutot–Carayol: at such an index the $\eta$-piece consists exactly of the classes of the $\Pi$-fixed-point-like elements $m\in M_i$ with $\Pi m=Vm$, parametrised injectively by $m$. It is stated over an arbitrary base of characteristic $p$ with $\Pi$-injectivity as an explicit hypothesis, so that it applies to geometric fibres, and it is cited by the computations of the $\eta$-pieces in degrees $0$ and $1$ over algebraically closed bases and by the resulting surjectivity and comparison statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP.lean

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

theorem CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_of_isCanonicalLMap_apply_eq_nMk_of_charP
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B)
    (X : FormalODModule p B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (htors : ∀ m : MvFormalGroup.CartierModule p X.F, MvFormalGroup.CartierModule.endAct X.varpiEnd m = 0 → m = 0)
    (i : Fin 2) (hi : ∀ m ∈ X.gradedPiece j (i : ℕ),
      ∃ g : MvFormalGroup.CartierModule p X.F, MvFormalGroup.CartierModule.verschiebungInt g = MvFormalGroup.CartierModule.endAct X.varpiEnd m)
    (hLi : ∀ x y : MvFormalGroup.CartierModule p X.F, x ∈ X.gradedPiece j (i : ℕ) →
      MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct X.varpiEnd x → L x = (X.toGradedCartierModuleData j hc).nMk (y, 0)) :
    (∀ z : (X.toGradedCartierModuleData j hc).NMod,
      z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i ↔
        ∃ m : MvFormalGroup.CartierModule p X.F, m ∈ X.gradedPiece j (i : ℕ) ∧
          MvFormalGroup.CartierModule.endAct X.varpiEnd m = MvFormalGroup.CartierModule.verschiebungInt m ∧ z = (X.toGradedCartierModuleData j hc).nMk (m, 0)) ∧
    (∀ m m' : MvFormalGroup.CartierModule p X.F, m ∈ X.gradedPiece j (i : ℕ) → m' ∈ X.gradedPiece j (i : ℕ) →
      (X.toGradedCartierModuleData j hc).nMk (m, 0) = (X.toGradedCartierModuleData j hc).nMk (m', 0) → m = m') := by sorry
