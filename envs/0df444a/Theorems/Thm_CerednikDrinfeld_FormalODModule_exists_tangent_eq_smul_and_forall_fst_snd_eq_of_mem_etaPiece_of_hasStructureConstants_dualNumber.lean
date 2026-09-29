-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_tangent_eq_smul_and_forall_fst_snd_eq_of_mem_etaPiece_of_hasStructureConstants_dualNumber
-- name    : CerednikDrinfeld.FormalODModule.exists_tangent_eq_smul_and_forall_fst_snd_eq_of_mem_etaPiece_of_hasStructureConstants_dualNumber
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/ae038b41-7ad9-5d92-b845-2c183341b815
-- title:
--   Tangent line of η_{i_0} over κ[ε] and its period equation
-- statement:
--   Let $p$ be a prime, $\kappa$ a field of characteristic $p$, $j\colon \mathbb W(\mathbb F_{p^2}) \to \kappa[\varepsilon]$ a ring homomorphism, and $X$ a formal $\mathcal O_D$-module over the dual numbers $\kappa[\varepsilon]$ (a commutative two-dimensional formal group law $F$ with an action of $\mathbb W(\mathbb F_{p^2})$ and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ a = \sigma(a)\circ\varpi$). Let $\gamma_0,\gamma_1$ be elements of the Cartier module of $F$ forming a homogeneous $V$-basis for $j$, i.e. $\gamma_i$ lies in the graded piece of degree $i$ (Teichmüller elements act through $j(\cdot)^{p^i}$) and the matrix of their tangents has unit determinant; assume the graded pieces of degrees $0$ and $1$ are complementary. Let $a,\nu\colon\mathbb N\to \mathrm{Fin}\,2\to\kappa$ and $c\in\kappa$ be such that $\gamma$ has structure constants $a_{m,i} + (c\,\nu_{m,i})\varepsilon$, meaning that for each $i$ and each $N$ one has $\varpi\gamma_i = \sum_{m<N} V^m\bigl([a_{m,i}+c\nu_{m,i}\varepsilon]\gamma_{\pi(m,i)}\bigr) + V^N h$ for some $h$, where $\pi(m,i)=(m+i+1)\bmod 2$ and $V$ is the integral Verschiebung; assume $\nu_{0,i}=0$ for all $i$, and fix $i_0$ with $a_{0,i_0}=0$. Let $L$ be an additive map from the Cartier module to the associated $N$-module which is a canonical $L$-map of the graded Cartier datum of $X$ (in particular $L(w\cdot x)=\sigma(w)\cdot L(x)$, $L(Vx)$ is the class of $(\varpi x,0)$, and $\lambda\circ L$ is Frobenius), let $z$ lie in $\eta(L)$ intersected with the degree-$i_0$ piece of the $N$-module, and let $m$ be a Cartier module element whose class modulo $V$ equals $u(z)$. Then there exists $x\in\kappa[\varepsilon]$ with $\mathrm{tangent}(m) = x\cdot \mathrm{tangent}(\gamma_{i_0})$, and for every such $x$, writing $a_1 = a_{0,\pi(0,i_0)}$, $i_1=\pi(0,i_0)$, $y$ for the first and $y'$ for the second component of $x$, $$a_1^{p} y = (a_1^{p}a_{1,i_0} + a_1 a_{1,i_1})y^{p} + (a_1^{p+1}a_{2,i_0} - a_1 a_{1,i_0}^{p}a_{1,i_1})y^{p^2},$$ $$a_1^{p} y' = c\Bigl((a_1^{p+1}\nu_{2,i_0} - a_1 a_{1,i_0}^{p}\nu_{1,i_1})y^{p^2} + (a_1^{p}\nu_{1,i_0} + a_1\nu_{1,i_1})y^{p}\Bigr).$$
--
--   This is the Boutot–Carayol reading of the line $u(\eta_{i_0})$ inside the Lie algebra of a first-order deformation of a special formal $\mathcal O_D$-module at an index where the leading structure constant vanishes: the $\kappa$-part of the tangent coordinate satisfies the period equation of the point, and its $\varepsilon$-part is an explicit additive polynomial in that part, proportional to the deformation parameter $c$. It is used to show that no first-order variation of the period can be of the prescribed multiplicative shape, and thence in the rigidity argument identifying Cartier quadruples by transport of the line away from nodes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_tangent_eq_smul_and_forall_fst_snd_eq_of_mem_etaPiece_of_hasStructureConstants_dualNumber.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_tangent_eq_smul_and_forall_fst_snd_eq_of_mem_etaPiece_of_hasStructureConstants_dualNumber
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p]
    (j : Zp2 p →+* DualNumber κ) (X : FormalODModule p (DualNumber κ))
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (a ν : ℕ → Fin 2 → κ) (c : κ)
    (hA : X.HasStructureConstants γ (fun m i => algebraMap κ (DualNumber κ) (a m i) + (c * ν m i) • DualNumber.eps))
    (hν0 : ∀ i, ν 0 i = 0) (i₀ : Fin 2) (ha0 : a 0 i₀ = 0)
    (L : (X.toGradedCartierModuleData j hc).M →+
      (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (z : (X.toGradedCartierModuleData j hc).NMod)
    (hz : z ∈ (X.toGradedCartierModuleData j hc).etaPiece L
      hL.isCartierLMap.map_verschiebung i₀)
    (m : CartierModule p X.F)
    (hm : (X.toGradedCartierModuleData j hc).vRange.mkQ m =
      (X.toGradedCartierModuleData j hc).u L
        hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz).1⟩) :
    (∃ x : DualNumber κ, tangent m = x • tangent (γ i₀)) ∧
    ∀ x : DualNumber κ, tangent m = x • tangent (γ i₀) →
      a 0 (FormalODModule.piIndex 0 i₀) ^ p * TrivSqZeroExt.fst x =
        (a 0 (FormalODModule.piIndex 0 i₀) ^ p * a 1 i₀ + a 0 (FormalODModule.piIndex 0 i₀) * a 1 (FormalODModule.piIndex 0 i₀)) *
            TrivSqZeroExt.fst x ^ p +
        (a 0 (FormalODModule.piIndex 0 i₀) ^ (p + 1) * a 2 i₀ -
            a 0 (FormalODModule.piIndex 0 i₀) * a 1 i₀ ^ p * a 1 (FormalODModule.piIndex 0 i₀)) * TrivSqZeroExt.fst x ^ (p ^ 2) ∧
      a 0 (FormalODModule.piIndex 0 i₀) ^ p * TrivSqZeroExt.snd x =
        c * ((a 0 (FormalODModule.piIndex 0 i₀) ^ (p + 1) * ν 2 i₀ -
              a 0 (FormalODModule.piIndex 0 i₀) * a 1 i₀ ^ p * ν 1 (FormalODModule.piIndex 0 i₀)) * TrivSqZeroExt.fst x ^ (p ^ 2) +
            (a 0 (FormalODModule.piIndex 0 i₀) ^ p * ν 1 i₀ + a 0 (FormalODModule.piIndex 0 i₀) * ν 1 (FormalODModule.piIndex 0 i₀)) *
              TrivSqZeroExt.fst x ^ p) := by sorry
