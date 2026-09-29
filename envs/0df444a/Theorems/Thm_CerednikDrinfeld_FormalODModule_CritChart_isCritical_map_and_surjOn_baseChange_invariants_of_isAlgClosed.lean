-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_and_surjOn_baseChange_invariants_of_isAlgClosed
-- name    : CerednikDrinfeld.FormalODModule.CritChart.isCritical_map_and_surjOn_baseChange_invariants_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/dac2e034-d55d-5409-b47f-0ca229b79c2b
-- title:
--   Critical index and its invariants under algebraically closed base change
-- statement:
--   Let $p$ be a prime and let $k$, $K$ be algebraically closed fields of characteristic $p$ (in the same universe). Let $j\colon \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to k$ be a ring homomorphism and let $X$ be a formal $\mathcal{O}_D$-module over $k$: a two-dimensional commutative formal group law $X.F$ with an additive, multiplicative action of $\mathbb{Z}_{p^2}$ by law endomorphisms together with a law endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ a = \sigma(a)\circ\varpi$. Assume $X$ is special for $j$, i.e. its Lie algebra is the direct sum of the submodules on which $\mathbb{Z}_{p^2}$ acts through $j$ and through $j\circ\sigma$, both invertible; and that $X$ has height $4$, i.e. the kernel algebra of the series giving the action of $p$ is finite projective over $k$ of rank $p^4$ over every field-valued base change. Let $g\colon k \to K$ be a ring homomorphism and let $i$ be a critical index for $(X,j)$: for every $m$ in the graded piece $M_i$ (those Cartier-module elements on which each Teichmüller lift $[c]$, $c \in \mathbb{F}_{p^2}$, acts as the homothety by $j([c])^{p^i}$) the element $\varpi\cdot m$ lies in the image of the Verschiebung. Then: (1) $i$ is a critical index for $(X_K, g\circ j)$, where $X_K$ is the base change of $X$ along $g$; (2) coefficientwise base change along $g$ sends the invariants $M_i^{\varpi = V} = \{m \in M_i : \varpi\cdot m = Vm\}$ of $X$ into those of $X_K$; and (3) every element of the invariants of $X_K$ at index $i$ is the base change of such an element for $X$.
--
--   At a critical index the invariants $M_i^{\varpi=V}$ compute the fibre of Drinfeld's étale sheaf $\eta$ at a geometric point, and the result says that this fibre is insensitive to enlarging the algebraically closed base field. It is used in the rigidified setting, where a fixed identification of $\eta$ at the base point must be transported along base change of geometric points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_CritChart_isCritical_map_and_surjOn_baseChange_invariants_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.CritChart.isCritical_map_and_surjOn_baseChange_invariants_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] {k K : Type u} [Field k] [IsAlgClosed k] [CharP k p]
    [Field K] [IsAlgClosed K] [CharP K p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (X : CerednikDrinfeld.FormalODModule p k)
    (hX : X.IsSpecial j) (hX4 : X.HasHeight 4) (g : k →+* K) (i : ℕ)
    (hi : CerednikDrinfeld.FormalODModule.CritChart.IsCritical X j i) :
    CerednikDrinfeld.FormalODModule.CritChart.IsCritical (X.map g) (g.comp j) i ∧
    (∀ m ∈ CerednikDrinfeld.FormalODModule.CritChart.invariants X j i,
      MvFormalGroup.CartierModule.baseChange (Φ := X.F) g m ∈
        CerednikDrinfeld.FormalODModule.CritChart.invariants (X.map g) (g.comp j) i) ∧
    (∀ m' ∈ CerednikDrinfeld.FormalODModule.CritChart.invariants (X.map g) (g.comp j) i,
      ∃ m ∈ CerednikDrinfeld.FormalODModule.CritChart.invariants X j i,
        MvFormalGroup.CartierModule.baseChange (Φ := X.F) g m = m') := by sorry
