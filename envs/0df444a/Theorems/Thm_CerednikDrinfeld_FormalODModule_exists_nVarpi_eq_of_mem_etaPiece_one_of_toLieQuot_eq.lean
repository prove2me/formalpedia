-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_nVarpi_eq_of_mem_etaPiece_one_of_toLieQuot_eq
-- name    : CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_one_of_toLieQuot_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/73ba54b8-eb10-5f8d-9801-dec925c41ca3
-- title:
--   Odd η-classes with tangent class Pi m₀ come from even ones
-- statement:
--   Let $p$ be a prime and $B$ a commutative ring of characteristic $p$, equipped with a ring homomorphism $j : W(\mathbb{F}_{p^2}) \to B$, and let $X$ be a formal $\mathcal{O}_D$-module over $B$: a $2$-dimensional commutative formal group law $F$ together with an action of $W(\mathbb{F}_{p^2})$ by law endomorphisms and a series $\varpi$ with $\varpi \circ \varpi = [p]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$. Write $M$ for the Cartier module of $F$ and, for $n$, let `gradedPiece` $j\,n$ be the subgroup of those $f \in M$ on which every Teichmüller element $c \in \mathbb{F}_{p^2}$ acts by the homothety $j(c)^{p^n}$. Assume `hc`, that `gradedPiece` $j\,0$ and `gradedPiece` $j\,1$ are complementary in $M$; let $D$ be the resulting graded Cartier module data, with Verschiebung `verschiebungInt`, Frobenius, and $\Pi$ the action of `varpiEnd`, and let $N = (M \times \Sigma)/\mathrm{nRel}$ be its `NMod`. Let $L : M \to N$ be an additive map which is a canonical $L$-map, i.e. a Cartier $L$-map admitting a lift along a surjection from a $p$-torsion-free ring carrying special graded Cartier module data. Assume: $\Pi m \in V M$ for every $m \in$ `gradedPiece` $j\,0$; and that whenever $x \in$ `gradedPiece` $j\,0$ and $V y = \Pi x$, then $L x = \mathrm{nMk}(y,0)$. Let $z$ lie in the degree-$1$ part `etaPiece` $L\,\cdot\,1$ of the $\eta$-subgroup of $N$, and suppose its image under `toLieQuot` in $M/VM$ is the class of $\Pi m_0$ for some $m_0 \in$ `gradedPiece` $j\,0$. Then there is $z_0$ in the degree-$0$ part `etaPiece` $L\,\cdot\,0$ with `nVarpi` $z_0 = z$, where `nVarpi` is induced by $\Pi$ on both coordinates.
--
--   This is a fibre computation for Drinfeld's condition on formal $\mathcal{O}_D$-modules in the Čerednik–Drinfeld uniformisation: in the case where the index $0$ is critical, the odd part of the $\eta$-locus is reached by $\Pi$ from its even part, as soon as the tangent class of the given odd invariant is of the form $\Pi m_0$ with $m_0$ even. It is used in the variant of the statement over a base with algebraically closed residue situation, [`CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_of_toLieQuot_eq_of_isAlgClosed`](thm.html#CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_of_toLieQuot_eq_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_nVarpi_eq_of_mem_etaPiece_one_of_toLieQuot_eq.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_one_of_toLieQuot_eq
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B)
    (X : FormalODModule p B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (h0 : ∀ m ∈ X.gradedPiece j 0, ∃ g : MvFormalGroup.CartierModule p X.F, MvFormalGroup.CartierModule.verschiebungInt g = MvFormalGroup.CartierModule.endAct X.varpiEnd m)
    (hL0 : ∀ x y : MvFormalGroup.CartierModule p X.F, x ∈ X.gradedPiece j 0 →
      MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct X.varpiEnd x → L x = (X.toGradedCartierModuleData j hc).nMk (y, 0))
    (z : (X.toGradedCartierModuleData j hc).NMod) (hz : z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 1)
    (htan : ∃ m₀ ∈ X.gradedPiece j 0, (X.toGradedCartierModuleData j hc).toLieQuot z = (X.toGradedCartierModuleData j hc).vRange.mkQ (MvFormalGroup.CartierModule.endAct X.varpiEnd m₀)) :
    ∃ z₀ ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 0, (X.toGradedCartierModuleData j hc).nVarpi z₀ = z := by sorry
