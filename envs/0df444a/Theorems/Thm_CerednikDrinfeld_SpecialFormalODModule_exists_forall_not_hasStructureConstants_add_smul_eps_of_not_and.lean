-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_forall_not_hasStructureConstants_add_smul_eps_of_not_and
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_forall_not_hasStructureConstants_add_smul_eps_of_not_and
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/d0e6fc64-8690-5bdb-b1ac-8f71cdc07a68
-- title:
--   First-order obstruction to structure constants at a smooth point
-- statement:
--   Let $q$ be a prime and $k$ an algebraically closed field of characteristic $q$, let $j_0\colon W(\mathbb F_{q^2})\to k$ be a ring homomorphism, and let $X_0$ be a special formal $\mathcal O_D$-module over $k$ relative to $j_0$: a two-dimensional commutative formal group law over $k$ together with an action of $W(\mathbb F_{q^2})$ and a law endomorphism $\varpi$ satisfying $\varpi\circ\varpi=[q]$ and $\varpi\circ[a]=[\mathrm{Frob}\,a]\circ\varpi$, whose Lie algebra is the direct sum of the two complementary invertible eigenspaces `lieZero` and `lieOne` for $j_0$ and its Frobenius twist, and with $\ker[q]$ of degree $q^4$. Assume the smoothness hypothesis that it is not the case that the linear part of $\varpi$ annihilates both `lieZero` and `lieOne`. Let $\gamma=(\gamma_0,\gamma_1)$ be a homogeneous $V$-basis of the Cartier module of $X_0$: $\gamma_i$ lies in the $i$-th graded piece for $j_0$ and the matrix of tangents of the $\gamma_i$ has invertible determinant. Let $a\colon\mathbb N\times\{0,1\}\to k$ be structure constants for $\gamma$, meaning that for all $i$ and all $N$ the image of $\gamma_i$ under $\varpi$ equals $\sum_{m<N}V^m([a_{m,i}]\gamma_{\pi(m,i)})$ modulo $V^N$, where $\pi(m,i)\equiv m+i+1 \bmod 2$, and suppose $a_{0,0}a_{0,1}=q$ in $k$. Then there is a variation $\delta a\colon\mathbb N\times\{0,1\}\to k$ with $\delta a_{0,i}=0$ for $i=0,1$ such that no homogeneous $V$-basis $\gamma'$ of the base change of $X_0$ along $k\to k[\varepsilon]$, relative to the composite of $j_0$ with $k\to k[\varepsilon]$, has structure constants $(m,i)\mapsto a_{m,i}+\delta a_{m,i}\varepsilon$.
--
--   This is the first-order non-triviality statement in the deformation theory of special formal $\mathcal O_D$-modules of height $4$ at a smooth point of the moduli problem: the family obtained by varying the structure constants in the directions $\delta a$ is not realised over the dual numbers by any homogeneous $V$-basis of the trivial deformation. It is the input used by [`CerednikDrinfeld.SpecialFormalODModule.exists_algHom_powerSeries_surjective_of_isProrepresentedBy_deformations_of_not_and`](thm.html#CerednikDrinfeld.SpecialFormalODModule.exists_algHom_powerSeries_surjective_of_isProrepresentedBy_deformations_of_not_and), which upgrades this tangent-level statement to a surjection from a power series ring onto the deformation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_forall_not_hasStructureConstants_add_smul_eps_of_not_and.lean

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

theorem CerednikDrinfeld.SpecialFormalODModule.exists_forall_not_hasStructureConstants_add_smul_eps_of_not_and
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
        (∀ m ∈ X₀.toFormalODModule.lieOne j₀, Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)))
    (γ : Fin 2 → MvFormalGroup.CartierModule q X₀.F) (hγ : X₀.toFormalODModule.IsHomogeneousVBasis j₀ γ)
    (a : ℕ → Fin 2 → k) (ha : X₀.toFormalODModule.HasStructureConstants γ a) (h01 : a 0 0 * a 0 1 = (q : k)) :
    ∃ δa : ℕ → Fin 2 → k, (∀ i, δa 0 i = 0) ∧
      ∀ (γ' : Fin 2 → MvFormalGroup.CartierModule q (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).F),
        (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).IsHomogeneousVBasis
            ((algebraMap k (DualNumber k)).comp j₀) γ' →
        ¬ (X₀.toFormalODModule.map (algebraMap k (DualNumber k))).HasStructureConstants γ'
            (fun m i => algebraMap k (DualNumber k) (a m i) + δa m i • DualNumber.eps) := by sorry
