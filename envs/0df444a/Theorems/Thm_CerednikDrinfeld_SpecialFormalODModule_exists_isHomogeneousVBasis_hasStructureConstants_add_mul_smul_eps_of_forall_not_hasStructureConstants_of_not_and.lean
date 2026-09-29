-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_isHomogeneousVBasis_hasStructureConstants_add_mul_smul_eps_of_forall_not_hasStructureConstants_of_not_and
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_isHomogeneousVBasis_hasStructureConstants_add_mul_smul_eps_of_forall_not_hasStructureConstants_of_not_and
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/d9a0ae74-b2ab-5ebd-a63c-215c7c8bf083
-- title:
--   First-order versality of a structure-constant line at a smooth point
-- statement:
--   Let $q$ be a prime, $k$ an algebraically closed field of characteristic $q$, and $j_0\colon W(\mathbb F_{q^2})\to k$ a ring homomorphism. Let $X_0$ be a special formal $\mathcal O_D$-module over $k$ relative to $j_0$: a two-dimensional commutative formal group law $F$ with an action of $W(\mathbb F_{q^2})$ by endomorphisms of $F$ and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi=[q]$ and $\varpi\circ[a]=[\mathrm{Frob}\,a]\circ\varpi$, such that the Lie algebra is the direct sum of the submodule where $W(\mathbb F_{q^2})$ acts through $j_0$ and the one where it acts through $j_0\circ\mathrm{Frob}$, both invertible, and such that $[q]$ has kernel of degree $q^4$. Assume the smoothness hypothesis that the linear part of $\varpi$ does not annihilate both of these two Lie submodules simultaneously. Let $\gamma=(\gamma_0,\gamma_1)$ be a homogeneous $V$-basis of the Cartier module of $F$ for $j_0$, that is, $\gamma_i$ lies in the $i$-th graded piece (for every $c\in\mathbb F_{q^2}$ the Teichmüller element $[c]$ acts on $\gamma_i$ by the homothety $j_0([c])^{q^i}$) and the $2\times 2$ matrix of tangent vectors of the $\gamma_i$ has unit determinant. Let $a\colon\mathbb N\to(\mathrm{Fin}\,2\to k)$ be structure constants for $\gamma$, in the sense that for each $i$ and each $N$ the image of $\gamma_i$ under $\varpi$ equals $\sum_{m<N}V^m\bigl(a_{m,i}\cdot\gamma_{(m+i+1)\bmod 2}\bigr)$ modulo $V^N$ of the Cartier module, where $V$ is the integral Verschiebung and $a_{m,i}\cdot$ denotes the homothety; assume $a_{0,0}a_{0,1}=q$ in $k$. Let $\nu\colon\mathbb N\to(\mathrm{Fin}\,2\to k)$ satisfy $\nu_{0,i}=0$ for both $i$, and assume that no homogeneous $V$-basis of the base change of $X_0$ along $k\to k[\varepsilon]$ (homogeneous for $j_0$ followed by $k\to k[\varepsilon]$) has structure constants $m,i\mapsto a_{m,i}+\nu_{m,i}\varepsilon$. Finally let $N$ be a formal $\mathcal O_D$-module over the dual numbers $k[\varepsilon]$ together with an isomorphism $w$ from the base change of $N$ along $k[\varepsilon]\to k$ to $X_0$. Then there exist $c\in k$ and a homogeneous $V$-basis $\gamma^N$ of the Cartier module of $N$ for $j_0$ followed by $k\to k[\varepsilon]$ whose structure constants are $m,i\mapsto a_{m,i}+c\,\nu_{m,i}\varepsilon$, and such that for each $i$ the base change of $\gamma^N_i$ along $k[\varepsilon]\to k$, pushed forward along the law homomorphism underlying $w$, equals $\gamma_i$.
--
--   This is the first-order versality statement for the one-parameter family of structure constants $a+c\,\nu\,\varepsilon$ at a smooth point of Drinfeld's moduli problem for special formal $\mathcal O_D$-modules: under the smoothness hypothesis every first-order deformation of $X_0$ is obtained, in the currency of structure constants of a homogeneous $V$-basis lifting $\gamma$, by rescaling the fixed non-trivial variation $\nu$. It is used in the smooth branch of the first-order rigidity of rigidified triples, [`CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.isIsomorphic_of_line_transport_of_not_node`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadrupleVia.isIsomorphic_of_line_transport_of_not_node).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_isHomogeneousVBasis_hasStructureConstants_add_mul_smul_eps_of_forall_not_hasStructureConstants_of_not_and.lean

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

theorem CerednikDrinfeld.SpecialFormalODModule.exists_isHomogeneousVBasis_hasStructureConstants_add_mul_smul_eps_of_forall_not_hasStructureConstants_of_not_and
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
        (∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)))
    (γ : Fin 2 → MvFormalGroup.CartierModule q X₀.F) (hγ : X₀.toFormalODModule.IsHomogeneousVBasis j₀ γ)
    (a : ℕ → Fin 2 → k) (ha : X₀.toFormalODModule.HasStructureConstants γ a) (h01 : a 0 0 * a 0 1 = (q : k))
    (ν : ℕ → Fin 2 → k) (hν0 : ∀ i, ν 0 i = 0)
    (hν : ∀ (γ' : Fin 2 → MvFormalGroup.CartierModule q (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).F),
        (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).IsHomogeneousVBasis
            ((algebraMap k (DualNumber k)).comp j₀) γ' →
        ¬ (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).HasStructureConstants γ'
            (fun m i => algebraMap k (DualNumber k) (a m i) + ν m i • DualNumber.eps))
    (N : FormalODModule q (DualNumber k))
    (w : (N.map (TrivSqZeroExt.fstHom k k k).toRingHom).Hom X₀.toFormalODModule) (hw : w.IsIso) :
    ∃ (c : k) (γN : Fin 2 → MvFormalGroup.CartierModule q N.F),
      N.IsHomogeneousVBasis ((algebraMap k (DualNumber k)).comp j₀) γN ∧
      N.HasStructureConstants γN (fun m i => algebraMap k (DualNumber k) (a m i) + (c * ν m i) • DualNumber.eps) ∧
      ∀ i, MvFormalGroup.CartierModule.map w.toLawHom
          (MvFormalGroup.CartierModule.baseChange (TrivSqZeroExt.fstHom k k k).toRingHom (γN i)) = γ i := by sorry
