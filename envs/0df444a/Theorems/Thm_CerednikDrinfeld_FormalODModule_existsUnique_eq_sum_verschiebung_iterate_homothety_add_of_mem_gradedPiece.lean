-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_existsUnique_eq_sum_verschiebung_iterate_homothety_add_of_mem_gradedPiece
-- name    : CerednikDrinfeld.FormalODModule.existsUnique_eq_sum_verschiebung_iterate_homothety_add_of_mem_gradedPiece
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/ea723f66-e1e2-5647-83fe-2cc12b20c19f
-- title:
--   Graded finite V-adic expansion in a homogeneous V-basis
-- statement:
--   Let $p$ be a prime, let $B$ be a commutative ring of characteristic $p$, write $\mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2})$ for [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17), and let $j : \mathbb{Z}_{p^2} \to B$ be a ring homomorphism. Let $X$ be a formal $\mathcal{O}_D$-module over $B$, that is, a commutative formal group law $F = X.F$ in two variables over $B$ together with an action $a \mapsto X.\mathrm{act}(a)$ of $\mathbb{Z}_{p^2}$ by endomorphisms of the law, additive and multiplicative in $a$, and a series $\varpi$ which is an endomorphism of the law with $\varpi \circ \varpi = X.\mathrm{act}(p)$ and $\varpi \circ X.\mathrm{act}(a) = X.\mathrm{act}(\mathrm{Frob}\,a) \circ \varpi$. Assume the two eigen-submodules of $\operatorname{Lie} X$ are complementary: $X.\mathrm{lieZero}\,j = \bigcap_a \ker(\mathrm{lieAct}(a) - j(a)\,\mathrm{id})$ and $X.\mathrm{lieOne}\,j = \bigcap_a \ker(\mathrm{lieAct}(a) - j(\mathrm{Frob}\,a)\,\mathrm{id})$ form an `IsCompl` pair. Let $M =$ `CartierModule p X.F`, with Verschiebung $V$ and homotheties $\langle b \rangle$ for $b \in B$, and for $n \in \mathbb{N}$ let $M_n = X.\mathrm{gradedPiece}\,j\,n$ be the additive subgroup of those $f \in M$ with $\mathrm{endAct}(X.\mathrm{actEnd}(\tau(c)))f = \langle j(\tau(c))^{p^n} \rangle f$ for every $c \in \mathbb{F}_{p^2}$, where $\tau$ is the Teichmüller lift. Let $\gamma : \{0,1\} \to M$ satisfy `IsHomogeneousVBasis`, i.e. $\gamma_l \in M_l$ for $l = 0,1$ and the $2 \times 2$ matrix of tangent vectors $(\mathrm{tangent}(\gamma_l)_k)$ has unit determinant. Then for all $i, N \in \mathbb{N}$ and every $m \in M_i$ there is exactly one pair $(a, g)$ with $a : \{0,\dots,N-1\} \to B$ and $g \in M$ such that $g \in M_{i+N}$ and $m = \sum_{k<N} V^k\big(\langle a_k \rangle \gamma_{(i+k) \bmod 2}\big) + V^N g$.
--
--   This is the graded form of the finite $V$-adic expansion of an element of the Cartier module of a special formal $\mathcal{O}_D$-module in a homogeneous $V$-basis, as in Boutot–Carayol, chapter II, (1.5) and (2.3); the coefficients $(a_k)$ and the remainder $g$ provide the coordinate chart in which Drinfeld's functors are analysed. It follows from the ungraded expansion [`MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebung_homothety_add`](thm.html#MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebung_homothety_add) together with the graded decomposition and compatibilities recorded in [`CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne`](thm.html#CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne), and is used for the critical-chart and base-change statements about these functors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_existsUnique_eq_sum_verschiebung_iterate_homothety_add_of_mem_gradedPiece.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.existsUnique_eq_sum_verschiebung_iterate_homothety_add_of_mem_gradedPiece
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] [CharP B p]
    (j : CerednikDrinfeld.Zp2 p →+* B) (X : CerednikDrinfeld.FormalODModule p B)
    (hLie : IsCompl (X.lieZero j) (X.lieOne j))
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (i N : ℕ) (m : MvFormalGroup.CartierModule p X.F) (hm : m ∈ X.gradedPiece j i) :
    ∃! ag : (Fin N → B) × MvFormalGroup.CartierModule p X.F,
      ag.2 ∈ X.gradedPiece j (i + N) ∧
      m = (∑ k : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := X.F)))^[k]
              (MvFormalGroup.CartierModule.homothety (ag.1 k)
                (γ ⟨(i + k) % 2, Nat.mod_lt _ two_pos⟩))) +
          (⇑(MvFormalGroup.CartierModule.verschiebung (p := p) (Φ := X.F)))^[N] ag.2 := by sorry
