-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_nsmul_eq_zero_of_mem_eta_of_isAlgClosed
-- name    : CerednikDrinfeld.FormalODModule.eq_zero_of_nsmul_eq_zero_of_mem_eta_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/a557eb03-1583-5d9e-85eb-3ec4e4bcea43
-- title:
--   No p-torsion in η(L) over an algebraically closed field
-- statement:
--   Fix a prime $p$ and an algebraically closed field $K$ of characteristic $p$, together with a ring homomorphism $j\colon W(\mathbb{F}_{p^2})\to K$. Let $X$ be a formal $\mathcal{O}_D$-module over $K$: a $2$-dimensional commutative formal group law $F$ over $K$ equipped with an action of $W(\mathbb{F}_{p^2})$ by endomorphisms of $F$ and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ[a] = [\sigma a]\circ\varpi$. Write $M =$ `CartierModule p X.F`, and let $X.gradedPiece\ j\ n$ be the subgroup of those $f \in M$ with $[\omega(c)]\,f = \omega(j(\omega(c))^{p^n})\,f$ for every $c \in \mathbb{F}_{p^2}$, where $\omega$ denotes Teichmüller lifts. Assume given $\gamma\colon \mathrm{Fin}\,2 \to M$ which is a homogeneous $V$-basis, that is, $\gamma_i$ lies in the graded piece of degree $i$ and the $2\times 2$ matrix of tangent vectors $(\mathrm{tangent}(\gamma_i)_k)$ has unit determinant; assume also that the graded pieces of degrees $0$ and $1$ are complementary in $M$, giving the graded Cartier module data $D = X.toGradedCartierModuleData\ j\ hc$ (with $F$, $V$, $\varpi$ and the two pieces). Let $L\colon D.M \to D.NMod$ be an additive map which is a canonical $L$-map, and let $\zeta \in D.NMod$ lie in $D.eta\ L$, the kernel of $D.phi\ L - \mathrm{id}$, i.e. the fixed points of the operator attached to $L$. If $p\cdot\zeta = 0$ then $\zeta = 0$.
--
--   This is the absence of $p$-torsion in $\eta(L) = N(M)^{\varphi_L = 1}$ for a formal $\mathcal{O}_D$-module over an algebraically closed field of characteristic $p$, in the form used in the Čerednik–Drinfeld uniformisation of Shimura curves. It is the algebraically closed base case from which the corresponding statement over a reduced base, [`CerednikDrinfeld.FormalODModule.eq_zero_of_nsmul_eq_zero_of_mem_eta_of_isReduced`](thm.html#CerednikDrinfeld.FormalODModule.eq_zero_of_nsmul_eq_zero_of_mem_eta_of_isReduced), is obtained.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_nsmul_eq_zero_of_mem_eta_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega
  MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

theorem CerednikDrinfeld.FormalODModule.eq_zero_of_nsmul_eq_zero_of_mem_eta_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [IsAlgClosed K] [CharP K p]
    (j : Zp2 p →+* K) (X : FormalODModule p K)
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (ζ : (X.toGradedCartierModuleData j hc).NMod)
    (hζ : ζ ∈ (X.toGradedCartierModuleData j hc).eta L hL.isCartierLMap.map_verschiebung)
    (hp : p • ζ = 0) :
    ζ = 0 := by sorry
