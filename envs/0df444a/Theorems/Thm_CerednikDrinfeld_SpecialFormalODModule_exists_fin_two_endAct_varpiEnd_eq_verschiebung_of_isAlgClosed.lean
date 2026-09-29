-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_endAct_varpiEnd_eq_verschiebung_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_endAct_varpiEnd_eq_verschiebung_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/42156d32-5c0a-5c18-96be-ef5cde17bbe3
-- title:
--   Rank-two lattice with Pi = V in M₀
-- statement:
--   Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$, $j\colon W(\mathbb F_{p^2}) \to k$ a ring homomorphism, and $\Phi$ a special formal $\mathcal O_D$-module of height $4$ over $k$ relative to $j$: a two-dimensional commutative formal group law $\Phi.F$ over $k$ together with laws $\mathrm{act}\,a$ giving an action of $W(\mathbb F_{p^2})$ by endomorphisms of $\Phi.F$ and a law $\varpi$ with $\varpi \circ \varpi = \mathrm{act}\,p$ and $\varpi \circ \mathrm{act}\,a = \mathrm{act}(\sigma a) \circ \varpi$, such that the two Lie pieces $\mathrm{lieZero}\,j$ and $\mathrm{lieOne}\,j$ are complementary and each an invertible $k$-module, and such that $\mathrm{act}\,p$ has kernel of degree $p^4$. Write $M$ for the Cartier module $\mathrm{CartierModule}\,p\,\Phi.F$, with its $W(k)$-action, its Verschiebung $V$, and the action of $\varpi$ through $\mathrm{endAct}\,\Phi.\mathrm{varpiEnd}$; for $n \in \mathbb N$ let $M_n = \Phi.\mathrm{gradedPiece}\,j\,n$ be the subgroup of those $f$ with $\mathrm{act}$ of the Teichmüller lift of each $c \in \mathbb F_{p^2}$ acting on $f$ as the homothety by $j([c])^{p^n}$. Then there are $e_0, e_1 \in M_0$ with $\varpi_* e_r = V e_r$ for both $r$, linearly independent over $W(k)$ in the sense that $\sum_r w_r \cdot e_r = 0$ forces $w = 0$, such that every $f \in M_0$ satisfies $p f \in W(k)e_0 + W(k)e_1$ and every $f \in M_1$ satisfies $\varpi_* f \in W(k)e_0 + W(k)e_1$.
--
--   This is the lattice statement appearing inside the proof of uniqueness up to isogeny of special formal $\mathcal O_D$-modules of height $4$ over an algebraically closed field, in the form of a rank-two free $W(k)$-lattice inside the degree-zero graded piece of the Cartier module on which $\varpi$ acts as Verschiebung, squeezed between $p M_0 + \varpi_* M_1$ and $M_0$. It is the input used to construct an injective homomorphism of Cartier modules between any two such modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_endAct_varpiEnd_eq_verschiebung_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_endAct_varpiEnd_eq_verschiebung_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ : CerednikDrinfeld.SpecialFormalODModule p j) :
    ∃ e : Fin 2 → MvFormalGroup.CartierModule p Φ.F,
      (∀ r, e r ∈ Φ.gradedPiece j 0) ∧
      (∀ r, MvFormalGroup.CartierModule.endAct Φ.varpiEnd (e r) =
        MvFormalGroup.CartierModule.verschiebung (e r)) ∧
      (∀ w : Fin 2 → WittVector p k, ∑ r, w r • e r = 0 → w = 0) ∧
      (∀ f ∈ Φ.gradedPiece j 0, ∃ w : Fin 2 → WittVector p k,
        (p : WittVector p k) • f = ∑ r, w r • e r) ∧
      (∀ f ∈ Φ.gradedPiece j 1, ∃ w : Fin 2 → WittVector p k,
        MvFormalGroup.CartierModule.endAct Φ.varpiEnd f = ∑ r, w r • e r) := by sorry
