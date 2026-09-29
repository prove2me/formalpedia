-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/b5055afe-8397-5e0e-ba02-a6bd48e6c72b
-- title:
--   Frobenius-fixed W(k)-basis at a critical index
-- statement:
--   Let $p$ be a prime and let $k$ be an algebraically closed field of characteristic $p$. Fix a ring homomorphism $j \colon \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to k$ and a special formal $\mathcal{O}_D$-module $\Phi$ over $k$ relative to $j$, that is, a two-dimensional commutative formal group law $\Phi.F$ over $k$ with an action of $\mathbb{Z}_{p^2}$ and an endomorphism-like series $\varpi$ satisfying $\varpi \circ \varpi = [p]$ and $\varpi \circ [a] = [\sigma(a)] \circ \varpi$, together with the properties `IsSpecial` relative to $j$ and `HasHeight 4`. Write $M =$ `CartierModule p Φ.F`, let $V$ be Verschiebung, let $\Pi$ be the action of `Φ.varpiEnd` through `endAct`, and let $M_i =$ `Φ.gradedPiece j i` be the subgroup of those $f \in M$ with $[\,\tau(c)\,]f = j(\tau(c))^{p^i} f$ for all $c \in \mathbb{F}_{p^2}$, where $\tau$ denotes the Teichmüller lift and the right-hand side is a homothety. Assume $i \in \mathbb{N}$ is critical, i.e. for every $m \in M_i$ there is $g \in M$ with $V g = \Pi m$. Then there exist $e_0, e_1 \in M$ such that: each $e_r$ lies in the invariants at $i$, namely $e_r \in M_i$ and $\Pi e_r = V e_r$; every $m \in M_i$ is uniquely $m = \sum_r w_r \cdot e_r$ with $w \colon \mathrm{Fin}\,2 \to W(k)$; for arbitrary $w$, the element $\sum_r w_r \cdot e_r$ satisfies $\Pi m = V m$ (and lies in $M_i$) if and only if each $w_r$ is fixed by the Frobenius of $W(k)$; for every $m \in M_i$ there is $g \in M_i$ with $\Pi m = V g$; and for every $g \in M_i$ there is $m \in M_i$ with $V g = \Pi m$.
--
--   This is the structural description of a graded piece at a critical index: $u = V^{-1}\Pi$ is a bijective $\sigma$-linear endomorphism of $M_i$, so $(M_i, u)$ is a unit-root $F$-crystal, $M_i$ has a $W(k)$-basis of $u$-fixed vectors, and the $u$-fixed points form a free $\mathbb{Z}_p$-module of rank $2$ spanning $M_i$ over $W(k)$; the last two clauses record $\Pi M_i = V M_i$. It is used by the results on critical charts, in particular the compatibility of criticality and of invariants with base change and the construction of the maps on the $\eta$-pieces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical.lean

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

theorem CerednikDrinfeld.SpecialFormalODModule.exists_fin_two_mem_invariants_forall_existsUnique_eq_sum_smul_of_isCritical
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ : CerednikDrinfeld.SpecialFormalODModule p j) (i : ℕ)
    (hi : CerednikDrinfeld.FormalODModule.CritChart.IsCritical Φ.toFormalODModule j i) :
    ∃ e : Fin 2 → MvFormalGroup.CartierModule p Φ.F,
      (∀ r, e r ∈ CerednikDrinfeld.FormalODModule.CritChart.invariants Φ.toFormalODModule j i) ∧
      (∀ m ∈ Φ.gradedPiece j i, ∃! w : Fin 2 → WittVector p k, m = ∑ r, w r • e r) ∧
      (∀ w : Fin 2 → WittVector p k,
        (∑ r, w r • e r) ∈ CerednikDrinfeld.FormalODModule.CritChart.invariants Φ.toFormalODModule j i ↔
          ∀ r, WittVector.frobenius (w r) = w r) ∧
      (∀ m ∈ Φ.gradedPiece j i, ∃ g ∈ Φ.gradedPiece j i,
        MvFormalGroup.CartierModule.endAct Φ.varpiEnd m = MvFormalGroup.CartierModule.verschiebung g) ∧
      (∀ g ∈ Φ.gradedPiece j i, ∃ m ∈ Φ.gradedPiece j i,
        MvFormalGroup.CartierModule.verschiebung g = MvFormalGroup.CartierModule.endAct Φ.varpiEnd m) := by sorry
