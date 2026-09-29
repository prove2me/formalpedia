-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_apply_mkQ_eq_mkQ_and_mem_vRange_iff_of_apply_eq_nMk_of_isCritical_of_isAlgClosed
-- name    : CerednikDrinfeld.FormalODModule.apply_mkQ_eq_mkQ_and_mem_vRange_iff_of_apply_eq_nMk_of_isCritical_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/917b0c44-9af4-5af8-b9e2-d9bc4b9d4888
-- title:
--   Compatibility of Theta with τ and V-divisibility on a critical piece
-- statement:
--   Fix a prime $p$ and an algebraically closed field $K$ of characteristic $p$, together with a ring homomorphism $j : W(\mathbb F_{p^2}) \to K$. Let $X$ and $X'$ be formal $\mathcal O_D$-modules over $K$ (two-dimensional commutative formal group laws with an action of $W(\mathbb F_{p^2})$ and an endomorphism $\varpi$ with $\varpi^2 = p$ and $\varpi a = a^\sigma \varpi$) that are special with respect to $j$, in the sense that the $j$- and $j\circ\sigma$-eigenspaces of the Lie algebra are complementary and invertible, and that have height $4$, i.e. the kernel of multiplication by $p$ has degree $p^4$. Assume the degree-$0$ and degree-$1$ graded pieces of the Cartier modules of $X$ and of $X'$, namely the subgroups on which the Teichmüller action of $c \in \mathbb F_{p^2}$ is homothety by $j(c)^{p^n}$, are complementary, giving graded Cartier module data $D$ and $D'$ with $M = \mathrm{Cart}_p(X)$, $M' = \mathrm{Cart}_p(X')$, Verschiebung $V$ the integral Verschiebung, and $\varpi$ acting. Let $L$ and $L'$ be canonical $L$-maps for $D$ and $D'$, let $i \in \{0,1\}$, and assume the index $i$ is critical for $X$: for every $m$ in the graded piece $i$, $\varpi m$ lies in the image of $V$. Let $\theta_\eta$ be an additive map from $\eta_i(L) = \eta(L) \cap N_i$ in $N = (M \times M^{(\sigma)})/\mathrm{nRel}$ to the corresponding $\eta_i(L')$ in $N'$, let $\tau : M/VM \to M'/V'M'$ be an injective $W(K)$-linear map, and assume: whenever $\mathrm{nMk}(m,0) \in \eta_i(L)$ and $\theta_\eta$ sends it to $\mathrm{nMk}(m',0)$, one has $\tau[m] = [m']$; and a $W(K)$-linear $\Theta : M \to M'$ satisfies $\theta_\eta(\mathrm{nMk}(m,0)) = \mathrm{nMk}(\Theta m, 0)$ for all such $m$. Then for every $x$ in the graded piece $i$ of $X$ one has $\tau[x] = [\Theta x]$ in $M'/V'M'$, and $x \in VM$ if and only if $\Theta x \in V'M'$.
--
--   This is the $V$-descent step in the Čerednik–Drinfeld comparison of special formal $\mathcal O_D$-modules through their graded Cartier modules: a bijection on the $\eta_i$-pieces, once extended to a $W(K)$-linear map $\Theta$ compatible with $\tau$ on the Lie quotients, transports divisibility by Verschiebung on the critical graded piece. It is used in the construction of a bijective morphism of Cartier modules in the rigidified Cartier quadruple setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_apply_mkQ_eq_mkQ_and_mem_vRange_iff_of_apply_eq_nMk_of_isCritical_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalODModule.apply_mkQ_eq_mkQ_and_mem_vRange_iff_of_apply_eq_nMk_of_isCritical_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [IsAlgClosed K] (j : Zp2 p →+* K)
    (X X' : FormalODModule p K) (hX : X.IsSpecial j) (hX4 : X.HasHeight 4)
    (hX' : X'.IsSpecial j) (hX'4 : X'.HasHeight 4)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1)) (hc' : IsCompl (X'.gradedPiece j 0) (X'.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod) (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (L' : (X'.toGradedCartierModuleData j hc').M →+ (X'.toGradedCartierModuleData j hc').NMod) (hL' : (X'.toGradedCartierModuleData j hc').IsCanonicalLMap L')
    (i : Fin 2)
    (hi : ∀ m ∈ X.gradedPiece j (i : ℕ), ∃ y : MvFormalGroup.CartierModule p X.F,
      MvFormalGroup.CartierModule.verschiebungInt y = MvFormalGroup.CartierModule.endAct X.varpiEnd m)
    (θη : (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i →+ (X'.toGradedCartierModuleData j hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i)
    (τ : (X.toGradedCartierModuleData j hc).LieQuot →ₗ[WittVector p K] (X'.toGradedCartierModuleData j hc').LieQuot) (hτ : Function.Injective τ)
    (hcompat : ∀ (m : (X.toGradedCartierModuleData j hc).M) (m' : (X'.toGradedCartierModuleData j hc').M) (hm : (X.toGradedCartierModuleData j hc).nMk (m, 0) ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i),
      ((θη ⟨(X.toGradedCartierModuleData j hc).nMk (m, 0), hm⟩ : (X'.toGradedCartierModuleData j hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i) : (X'.toGradedCartierModuleData j hc').NMod) = (X'.toGradedCartierModuleData j hc').nMk (m', 0) →
        τ ((X.toGradedCartierModuleData j hc).vRange.mkQ m) = (X'.toGradedCartierModuleData j hc').vRange.mkQ m')
    (Θ : MvFormalGroup.CartierModule p X.F →ₗ[WittVector p K] MvFormalGroup.CartierModule p X'.F)
    (hΘ : ∀ (m : (X.toGradedCartierModuleData j hc).M) (hm : (X.toGradedCartierModuleData j hc).nMk (m, 0) ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i),
      ((θη ⟨(X.toGradedCartierModuleData j hc).nMk (m, 0), hm⟩ : (X'.toGradedCartierModuleData j hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i) : (X'.toGradedCartierModuleData j hc').NMod) = (X'.toGradedCartierModuleData j hc').nMk (Θ m, 0)) :
    ∀ x ∈ X.gradedPiece j (i : ℕ),
      τ ((X.toGradedCartierModuleData j hc).vRange.mkQ x) = (X'.toGradedCartierModuleData j hc').vRange.mkQ (Θ x) ∧
      ((∃ y : MvFormalGroup.CartierModule p X.F, MvFormalGroup.CartierModule.verschiebungInt y = x) ↔
        (∃ y' : MvFormalGroup.CartierModule p X'.F, MvFormalGroup.CartierModule.verschiebungInt y' = Θ x)) := by sorry
