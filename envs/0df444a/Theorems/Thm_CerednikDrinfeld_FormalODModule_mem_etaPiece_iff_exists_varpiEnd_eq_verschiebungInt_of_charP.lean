-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_mem_etaPiece_iff_exists_varpiEnd_eq_verschiebungInt_of_charP
-- name    : CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_exists_varpiEnd_eq_verschiebungInt_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/742ae057-19c1-5fca-bfe4-488a6ba8aaa2
-- title:
--   η at a critical index over a base of characteristic p
-- statement:
--   Let $p$ be a prime, $B$ a commutative ring with $\operatorname{char} B = p$, $j : W(\mathbb{F}_{p^2}) \to B$ a ring homomorphism and $X$ a formal $\mathcal{O}_D$-module over $B$, i.e. a commutative $2$-dimensional formal group law $F$ over $B$ together with an action of $W(\mathbb{F}_{p^2})$ by law endomorphisms and a law endomorphism $\varpi$ with $\varpi \circ \varpi = [p]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$. Write $M$ for the Cartier module of $F$ and, for $n \in \mathbb{N}$, $M_n =$ `gradedPiece` $j\,n$ for the subgroup of those $f \in M$ on which every Teichmüller element $c \in \mathbb{F}_{p^2}$ acts by the homothety $j(\tau(c))^{p^n}$. Assume $M_0$ and $M_1$ are complementary, that the integral Verschiebung $V$ on $M$ is injective, that $L : M \to N(M)$ is an additive map which is a canonical $L$-map (a Cartier $L$-map admitting a lift along a surjection from a $p$-torsion-free ring carrying a special graded Cartier module datum), and that $i \in \{0,1\}$ is critical in the sense that $\Pi m := \varpi_* m$ lies in $V(M)$ for every $m \in M_i$. Then for $z \in N(M)$: $z$ lies in $\eta(L) \cap N(M)_i$ if and only if there is $m \in M_i$ with $\Pi m = V m$ and $z = ((m,0))$. Only existence of such an $m$ is asserted, not uniqueness.
--
--   This is Drinfeld's description of the module $\eta$ at a critical index, as in Boutot–Carayol, in a form valid over an arbitrary base of characteristic $p$ with injective Verschiebung, no injectivity of $\Pi$ (hence no uniqueness of the representative $m$) being assumed. It is used for the computations of $\eta$ and of tangent vectors over dual numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_mem_etaPiece_iff_exists_varpiEnd_eq_verschiebungInt_of_charP.lean

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

theorem CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_exists_varpiEnd_eq_verschiebungInt_of_charP
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B)
    (X : FormalODModule p B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (hV : Function.Injective (MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := X.F)))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (i : Fin 2) (hi : ∀ m ∈ X.gradedPiece j (i : ℕ),
      ∃ g : MvFormalGroup.CartierModule p X.F,
        MvFormalGroup.CartierModule.verschiebungInt g = MvFormalGroup.CartierModule.endAct X.varpiEnd m)
    (z : (X.toGradedCartierModuleData j hc).NMod) :
    z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i ↔
      ∃ m : MvFormalGroup.CartierModule p X.F, m ∈ X.gradedPiece j (i : ℕ) ∧
        MvFormalGroup.CartierModule.endAct X.varpiEnd m = MvFormalGroup.CartierModule.verschiebungInt m ∧
        z = (X.toGradedCartierModuleData j hc).nMk (m, 0) := by sorry
