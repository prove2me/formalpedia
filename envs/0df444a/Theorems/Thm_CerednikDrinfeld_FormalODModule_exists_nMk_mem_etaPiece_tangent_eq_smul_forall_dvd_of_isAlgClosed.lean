-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_nMk_mem_etaPiece_tangent_eq_smul_forall_dvd_of_isAlgClosed
-- name    : CerednikDrinfeld.FormalODModule.exists_nMk_mem_etaPiece_tangent_eq_smul_forall_dvd_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/7ee1636a-e5d5-5241-baa1-8d4596411488
-- title:
--   Two η-elements at a critical index with 𝔽ₚ-independent tangents
-- statement:
--   Let $p$ be a prime and $\kappa$ an algebraically closed field of characteristic $p$, let $j\colon W(\mathbb{F}_{p^2})\to\kappa$ be a ring homomorphism, and let $Y$ be a formal $\mathcal{O}_D$-module over $\kappa$ (a two-dimensional commutative formal group law $Y.F$ with an action of $W(\mathbb{F}_{p^2})$ and a uniformiser endomorphism $\varpi$ satisfying $\varpi\circ\varpi=[p]$ and $\varpi\circ a=\sigma(a)\circ\varpi$) whose kernel of $[p]$ has degree $p^4$, expressed by `hY4 : Y.HasHeight 4`. Assume $\gamma_0,\gamma_1$ in the Cartier module $M$ of $Y.F$ form a homogeneous $V$-basis for $j$: $\gamma_i$ lies in the graded piece `gradedPiece j i`, on which every Teichmüller unit $c\in\mathbb{F}_{p^2}$ acts by the homothety $j(c)^{p^i}$, and the matrix of tangent vectors $(\,\mathrm{tangent}(\gamma_i)_k\,)$ has unit determinant; assume the two graded pieces for $0$ and $1$ are complementary, and that $a\colon\mathbb{N}\to\mathrm{Fin}\,2\to\kappa$ is a family of structure constants for $\gamma$, that is, for all $i$ and $N$ one has $\varpi\gamma_i=\sum_{m<N}V^m\big(\langle a_{m,i}\rangle\gamma_{\pi(m,i)}\big)+V^N h$ for some $h$, with $\pi(m,i)=(m+i+1)\bmod 2$ and $V$ the integral Verschiebung. Let $i_0$ be an index with $a_{0,i_0}=0$ while $a_{0,\pi(0,i_0)}\neq 0$. Finally let $D=Y.\mathrm{toGradedCartierModuleData}$ be the graded Cartier module data attached to $Y$, $j$ and the complementarity hypothesis (underlying module $M$, Frobenius and integral Verschiebung of the Cartier module, $\varpi$ acting through `varpiLinear`, pieces the two graded submodules), and let $L\colon M\to N$ be a canonical $L$-map for $D$: a Cartier $L$-map ($\sigma$-semilinear, $L(Vx)=\mathrm{nMk}(\varpi x,0)$, $\lambda\circ L=\mathrm{Frobenius}$) which moreover comes by base change from a Cartier $L$-map on a special graded Cartier module over a $p$-torsion-free ring surjecting onto $\kappa$. The conclusion asserts the existence of $m_1,m_2\in M$ and $y_1,y_2\in\kappa$ such that both $\mathrm{nMk}(m_1,0)$ and $\mathrm{nMk}(m_2,0)$ lie in `etaPiece L … i₀`, the intersection of the subgroup `eta L` with the image under $\mathrm{nMk}$ of $(\text{piece } i_0)\times(\text{piece } i_0)$, with $\mathrm{tangent}(m_1)=y_1\cdot\mathrm{tangent}(\gamma_{i_0})$ and $\mathrm{tangent}(m_2)=y_2\cdot\mathrm{tangent}(\gamma_{i_0})$, and such that for all integers $c_1,c_2$ with $c_1y_1+c_2y_2=0$ both $c_1$ and $c_2$ are divisible by $p$.
--
--   This is the geometric-point input to Drinfeld's description of the $\varpi$-invariant lattice $\eta$ attached to a special formal $\mathcal{O}_D$-module of height $4$: at a critical index $i_0$ the lattice contains two elements whose tangent coordinates along $\gamma_{i_0}$ remain independent over the prime field, so the induced map to the one-dimensional Lie piece has kernel exactly $p\eta_{i_0}$. It is used by the corresponding statement over the dual numbers, `exists_mem_etaPiece_tangent_eq_smul_forall_dvd_of_isAlgClosed_dualNumber`, in the Čerednik–Drinfeld uniformisation strand.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_nMk_mem_etaPiece_tangent_eq_smul_forall_dvd_of_isAlgClosed.lean

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
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

theorem CerednikDrinfeld.FormalODModule.exists_nMk_mem_etaPiece_tangent_eq_smul_forall_dvd_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]
    (j : Zp2 p →+* κ) (Y : FormalODModule p κ) (hY4 : Y.HasHeight 4)
    (γ : Fin 2 → CartierModule p Y.F) (hγ : Y.IsHomogeneousVBasis j γ)
    (hc : IsCompl (Y.gradedPiece j 0) (Y.gradedPiece j 1))
    (a : ℕ → Fin 2 → κ) (ha : Y.HasStructureConstants γ a)
    (i₀ : Fin 2) (ha0 : a 0 i₀ = 0) (ha1 : a 0 (FormalODModule.piIndex 0 i₀) ≠ 0)
    (L : (Y.toGradedCartierModuleData j hc).M →+ (Y.toGradedCartierModuleData j hc).NMod)
    (hL : (Y.toGradedCartierModuleData j hc).IsCanonicalLMap L) :
    ∃ (m₁ m₂ : CartierModule p Y.F) (y₁ y₂ : κ),
      (Y.toGradedCartierModuleData j hc).nMk (m₁, 0) ∈
        (Y.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i₀ ∧
      (Y.toGradedCartierModuleData j hc).nMk (m₂, 0) ∈
        (Y.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i₀ ∧
      tangent m₁ = y₁ • tangent (γ i₀) ∧ tangent m₂ = y₂ • tangent (γ i₀) ∧
      ∀ c₁ c₂ : ℤ, c₁ • y₁ + c₂ • y₂ = 0 → (p : ℤ) ∣ c₁ ∧ (p : ℤ) ∣ c₂ := by sorry
