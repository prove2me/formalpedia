-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_nVarpi_eq_of_mem_etaPiece_of_toLieQuot_eq_of_isAlgClosed
-- name    : CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_of_toLieQuot_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/760ca74d-b0ef-53c8-9f5e-2f7e778a2a8b
-- title:
--   Condition [C2] for η-invariants over an algebraically closed field
-- statement:
--   Let $p$ be a prime, $K$ an algebraically closed field of characteristic $p$ and $j\colon \mathbb{Z}_{p^2}=W(\mathbb{F}_{p^2})\to K$ a ring homomorphism. Let $X$ be a formal $\mathcal{O}_D$-module over $K$, i.e. a $2$-dimensional commutative formal group law $F$ together with an action of $W(\mathbb{F}_{p^2})$ by formal-group endomorphisms and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$. Assume $X$ is special for $j$ (its Lie algebra splits into two complementary invertible $j$-eigenpieces) and has height $4$ (the kernel of $[p]$ has degree $p^{4}$). Write $M$ for the Cartier module of $F$ and $M_n\subseteq M$ for the piece on which each Teichmüller lift $c$ acts by the homothety $j(c)^{p^{n}}$; assume $M_0$ and $M_1$ are complementary, giving the graded Cartier module data $D$ with $V$, $F$ and $\varpi$. Let $L\colon M\to N(M)$ be an additive map which is a canonical $L$-map, and let $\eta(L)_i=\eta(L)\cap N(M)_i$ for $i\in\{0,1\}$. The assertion is the conjunction, for $(i,i')=(0,1)$ and $(1,0)$, of: every $z\in\eta(L)_i$ whose image in $M/VM$ under the map induced by the first projection equals the class of $\varpi m$ for some $m\in M_{i'}$ is of the form $z=\varpi_N(z')$ for some $z'\in\eta(L)_{i'}$, where $\varpi_N$ is $\varpi$ acting coordinatewise on $N(M)$.
--
--   This is the fibrewise algebra behind Drinfeld's condition [C2] for the quadruple attached to a special formal $\mathcal{O}_D$-module: on the $\eta$-invariants, the classes killed in the Lie quotient by the relevant tangent condition are exactly those divisible by $\varpi$ coming from the opposite parity. It feeds the rigidified-deformation computation used in the Čerednik–Drinfeld uniformisation, being cited in the analysis of stalk maps and tangent germs over Witt vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_nVarpi_eq_of_mem_etaPiece_of_toLieQuot_eq_of_isAlgClosed.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_nVarpi_eq_of_mem_etaPiece_of_toLieQuot_eq_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [IsAlgClosed K] [CharP K p] (j : Zp2 p →+* K)
    (X : FormalODModule p K) (hX : X.IsSpecial j) (hX4 : X.HasHeight 4)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L) :
    (∀ z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 0,
      (∃ m₁ ∈ X.gradedPiece j 1, (X.toGradedCartierModuleData j hc).toLieQuot z =
          (X.toGradedCartierModuleData j hc).vRange.mkQ (MvFormalGroup.CartierModule.endAct X.varpiEnd m₁)) →
      ∃ z₁ ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 1, (X.toGradedCartierModuleData j hc).nVarpi z₁ = z) ∧
    (∀ z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 1,
      (∃ m₀ ∈ X.gradedPiece j 0, (X.toGradedCartierModuleData j hc).toLieQuot z =
          (X.toGradedCartierModuleData j hc).vRange.mkQ (MvFormalGroup.CartierModule.endAct X.varpiEnd m₀)) →
      ∃ z₀ ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung 0, (X.toGradedCartierModuleData j hc).nVarpi z₀ = z) := by sorry
