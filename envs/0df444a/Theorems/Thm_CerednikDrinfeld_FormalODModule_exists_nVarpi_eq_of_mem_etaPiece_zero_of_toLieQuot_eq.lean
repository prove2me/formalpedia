-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_nVarpi_eq_of_mem_etaPiece_zero_of_toLieQuot_eq
-- name    : CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_zero_of_toLieQuot_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/b5015983-4366-5aec-ac54-41fa1d20accb
-- title:
--   Even η-classes with tangent class in varpi Lie₁ come from η₁
-- statement:
--   Let $p$ be a prime, $B$ a commutative ring of characteristic $p$, $j : W(\mathbb{F}_{p^2}) \to B$ a ring homomorphism and $X$ a formal $\mathcal{O}_D$-module over $B$, that is, a commutative two-dimensional formal group law $F$ together with an action of $W(\mathbb{F}_{p^2})$ and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ a = \sigma(a)\circ\varpi$. Write $M$ for the Cartier module of $F$, with its Frobenius, its integral Verschiebung $V$ and the operator $\varpi$ induced by `varpiEnd`, and let `gradedPiece` $j\,n$ be the subgroup of those $f \in M$ with $a(c)\cdot f = j(\tau(c))^{p^n} f$ for every $c \in \mathbb{F}_{p^2}$, where $a(c)$ is the action of the Teichmüller lift and the right-hand side is the corresponding homothety. Assume the pieces of index $0$ and $1$ are complementary, giving the graded Cartier module data $D =$ `X.toGradedCartierModuleData j hc`, with $N = D.\mathrm{NMod}$ the quotient of $M \times \Sigma$ ($\Sigma$ being $M$ with Frobenius-twisted scalars) by `nRel`, with `nMk` the induced map from $M \times M$, with $\lambda(\mathrm{nMk}(a,b)) = \varpi a + V b$, with `toLieQuot` sending $\mathrm{nMk}(a,b)$ to the class of $a$ in $M/VM$, and with $\varpi_N(\mathrm{nMk}(a,b)) = \mathrm{nMk}(\varpi a, \varpi b)$. Let $L : M \to N$ be additive and satisfy `IsCanonicalLMap`, so in particular $L(wx) = \sigma(w)L(x)$, $L(Vx) = \mathrm{nMk}(\varpi x, 0)$ and $\lambda(L(x)) = \mathrm{Frob}(x)$, and write $\eta_i$ for the subgroup `etaPiece` $L\,i$, the intersection of the subgroup `eta` attached to $L$ with the image under `nMk` of the product of the $i$-th piece with itself. Assume: (i) $\eta_0$ consists exactly of the classes $\mathrm{nMk}(m,0)$ with $m$ in the piece of index $0$ and $\varpi m = V m$; (ii) every such $m$ which can be written as $\varpi m_1 + V g$ with $m_1$ in the piece of index $1$ and $g \in M$ equals $\lambda(z_1)$ for some $z_1 \in \eta_1$. Then for every $z \in \eta_0$ whose image under `toLieQuot` is the class of $\varpi m_1$ in $M/VM$ for some $m_1$ in the piece of index $1$, there exists $z_1 \in \eta_1$ with $\varpi_N z_1 = z$.
--
--   This is the fibrewise computation underlying Drinfeld's second condition on the even part of the $\eta$-filtration: an even $L$-invariant whose tangent class lies in $\varpi(\mathrm{Lie}_1)$ is the $\varpi_N$-image of an odd invariant. It is the hypothesis-laden form used to prove [`CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_of_toLieQuot_eq_of_isAlgClosed`](thm.html#CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_of_toLieQuot_eq_of_isAlgClosed), where conditions (i) and (ii) are verified over an algebraically closed base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_nVarpi_eq_of_mem_etaPiece_zero_of_toLieQuot_eq.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_zero_of_toLieQuot_eq
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B)
    (X : FormalODModule p B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (hEta0 : ∀ z : (X.toGradedCartierModuleData j hc).NMod, z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 0 ↔
      ∃ m : MvFormalGroup.CartierModule p X.F, m ∈ X.gradedPiece j 0 ∧ MvFormalGroup.CartierModule.endAct X.varpiEnd m = MvFormalGroup.CartierModule.verschiebungInt m ∧ z = (X.toGradedCartierModuleData j hc).nMk (m, 0))
    (hlift : ∀ m ∈ X.gradedPiece j 0, MvFormalGroup.CartierModule.endAct X.varpiEnd m = MvFormalGroup.CartierModule.verschiebungInt m →
      (∃ m₁ ∈ X.gradedPiece j 1, ∃ g : MvFormalGroup.CartierModule p X.F, m = MvFormalGroup.CartierModule.endAct X.varpiEnd m₁ + MvFormalGroup.CartierModule.verschiebungInt g) →
        ∃ z₁ ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 1, (X.toGradedCartierModuleData j hc).lambda z₁ = m)
    (z : (X.toGradedCartierModuleData j hc).NMod) (hz : z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 0)
    (htan : ∃ m₁ ∈ X.gradedPiece j 1, (X.toGradedCartierModuleData j hc).toLieQuot z = (X.toGradedCartierModuleData j hc).vRange.mkQ (MvFormalGroup.CartierModule.endAct X.varpiEnd m₁)) :
    ∃ z₁ ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 1, (X.toGradedCartierModuleData j hc).nVarpi z₁ = z := by sorry
