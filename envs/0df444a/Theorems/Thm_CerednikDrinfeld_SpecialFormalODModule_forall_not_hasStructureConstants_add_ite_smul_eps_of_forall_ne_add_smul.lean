-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_forall_not_hasStructureConstants_add_ite_smul_eps_of_forall_ne_add_smul
-- name    : CerednikDrinfeld.SpecialFormalODModule.forall_not_hasStructureConstants_add_ite_smul_eps_of_forall_ne_add_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/edd429f1-2a1f-50f5-b4ae-fb3fe974239f
-- title:
--   Unrealisable first-order variation of three structure constants
-- statement:
--   Let $q$ be a prime and $k$ an algebraically closed field of characteristic $q$, and let $j_0 : \mathrm{W}(\mathbf F_{q^2}) \to k$ be a ring homomorphism. Let $X_0$ be a term of `SpecialFormalODModule q j₀`, that is, a two-dimensional commutative formal group law $F$ over $k$ equipped with an action of $\mathrm{W}(\mathbf F_{q^2})$ and an endomorphism $\varpi$ with $\varpi\circ\varpi = [q]$ and $\varpi\circ a = \mathrm{Frob}(a)\circ\varpi$, subject to the predicates `IsSpecial` for $j_0$ and `HasHeight 4`. Let $\gamma_0,\gamma_1$ be elements of the Cartier module of $F$ forming a homogeneous $V$-basis for $j_0$: each $\gamma_i$ lies in the $i$-th graded piece and the matrix of their tangent vectors has unit determinant. Let $a : \mathbb N \to \mathrm{Fin}\,2 \to k$ be structure constants for $\gamma$, i.e. for each $i$ and each $N$ there is a Cartier module element $h$ with $\varpi\cdot\gamma_i = \sum_{m<N} V^m\big(a_{m,i}\,\gamma_{\pi(m,i)}\big) + V^N h$, where $\pi(m,i) = \mathrm{piIndex}\,m\,i = (m+i+1) \bmod 2$. Assume $a_{0,0}a_{0,1} = q$ in $k$, and fix $i_0$ with $a_{0,i_0} = 0$ and $e := a_{0,\pi(0,i_0)} \neq 0$. Let $\delta \in k^3$ satisfy: for all $v,s \in k$, $\delta \neq v\,(e,\,-e^q,\,-a_{1,i_0}^q) + s\,(-a_{1,i_0},\,-a_{1,\pi(0,i_0)},\,-a_{2,i_0})$, i.e. $\delta$ lies outside the plane spanned by those two vectors. The conclusion is that for every family $\gamma'$ of two elements of the Cartier module of the base change $X_0 \otimes_k k[\varepsilon]$ along $k \to \mathrm{DualNumber}\,k$ which is a homogeneous $V$-basis for $j_0$ composed with that map, $\gamma'$ does not have structure constants $a_{m,i} + \delta_{m,i}\varepsilon$, where the first-order term is $\delta_0$ at $(m,i) = (1,i_0)$, $\delta_1$ at $(1,\pi(0,i_0))$, $\delta_2$ at $(2,i_0)$, and $0$ at all other slots.
--
--   This is the negative half of a first-order versality computation for special formal $\mathcal O_D$-modules of height $4$ in the Čerednik–Drinfeld setting: the first-order variations of the three structure constants at the slots $(1,i_0)$, $(1,i_0+1)$, $(2,i_0)$ that can be produced on the trivial deformation $X_0 \otimes_k k[\varepsilon]$ by re-choosing the homogeneous $V$-basis fill exactly the plane spanned by the two displayed vectors, and nothing outside it is realised. It is used in the analysis of rigidified special formal $\mathcal O_D$-modules, in [`CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.isIsomorphic_of_line_transport_of_not_node`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.isIsomorphic_of_line_transport_of_not_node).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_forall_not_hasStructureConstants_add_ite_smul_eps_of_forall_ne_add_smul.lean

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

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in

theorem CerednikDrinfeld.SpecialFormalODModule.forall_not_hasStructureConstants_add_ite_smul_eps_of_forall_ne_add_smul
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (γ : Fin 2 → MvFormalGroup.CartierModule q X₀.F) (hγ : X₀.toFormalODModule.IsHomogeneousVBasis j₀ γ)
    (a : ℕ → Fin 2 → k) (ha : X₀.toFormalODModule.HasStructureConstants γ a) (h01 : a 0 0 * a 0 1 = (q : k))
    (i₀ : Fin 2) (ha0 : a 0 i₀ = 0) (hu : a 0 (FormalODModule.piIndex 0 i₀) ≠ 0)
    (δ : Fin 3 → k)
    (hδ : ∀ v s : k, δ ≠ v • ![a 0 (FormalODModule.piIndex 0 i₀), -(a 0 (FormalODModule.piIndex 0 i₀) ^ q), -(a 1 i₀ ^ q)] +
        s • ![-(a 1 i₀), -(a 1 (FormalODModule.piIndex 0 i₀)), -(a 2 i₀)]) :
    ∀ (γ' : Fin 2 → MvFormalGroup.CartierModule q (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).F),
      (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).IsHomogeneousVBasis
          ((algebraMap k (DualNumber k)).comp j₀) γ' →
      ¬ (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).HasStructureConstants γ'
          (fun m i => algebraMap k (DualNumber k) (a m i) +
            (if m = 1 ∧ i = i₀ then δ 0 else if m = 1 ∧ i = FormalODModule.piIndex 0 i₀ then δ 1
              else if m = 2 ∧ i = i₀ then δ 2 else 0) • DualNumber.eps) := by sorry
