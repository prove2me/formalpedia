-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_nsmul_eq_zero_of_mem_eta_of_isReduced
-- name    : CerednikDrinfeld.FormalODModule.eq_zero_of_nsmul_eq_zero_of_mem_eta_of_isReduced
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/2dc9c210-5764-5b04-932d-5cf5efb8ccff
-- title:
--   No p-torsion in η(L) over reduced Noetherian bases of characteristic p
-- statement:
--   Fix a prime $p$ and a commutative ring $S$ that is reduced and Noetherian and in which $p = 0$, together with a ring homomorphism $j \colon W(\mathbb F_{p^2}) \to S$. Let $X$ be a formal $\mathcal O_D$-module over $S$, that is, a commutative two-dimensional formal group law $F$ over $S$ equipped with an action of $W(\mathbb F_{p^2})$ by endomorphism series and a series $\varpi$ with $\varpi \circ \varpi = [p]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$. Let $\gamma \colon \mathrm{Fin}\,2 \to$ `CartierModule p X.F` be a homogeneous $V$-basis in the sense that $\gamma i$ lies in the $i$-th graded piece — the set of elements on which the Teichmüller endomorphism attached to each $c \in \mathbb F_{p^2}$ acts as the homothety by $j(\tau(c))^{p^{i}}$ — and the matrix of tangent coordinates $(\mathrm{tangent}(\gamma i)_k)$ has unit determinant; assume furthermore that the graded pieces of indices $0$ and $1$ are complementary subgroups, giving the graded Cartier module data $D = X.\mathtt{toGradedCartierModuleData}\ j\ hc$ with underlying module $M$ the Cartier module of $X$, its $F$, $V$ and $\varpi$ operators and its two pieces. Let $L \colon M \to N(M)$, where $N(M)$ is the quotient of $M \times D.\mathtt{Sigma}$ by the relation `nRel`, be a canonical $L$-map, i.e. a Cartier $L$-map that is compatible, via base change along a surjection from a $p$-torsion-free base carrying a special graded Cartier module datum, with an $L$-map there. Then every $\zeta \in N(M)$ lying in $\eta(L)$, the kernel of $\varphi_L - \mathrm{id}$ on $N(M)$, and satisfying $p \cdot \zeta = 0$, is zero.
--
--   This is the torsion-freeness part of the analysis of the module $\eta(L)$ attached to a formal $\mathcal O_D$-module in the Čerednik–Drinfeld uniformisation, in the form given by Boutot and Carayol; it reduces the general statement over a reduced Noetherian base of characteristic $p$ to the case of an algebraically closed field by embedding $S$ into a product of perfect residue fields at its minimal primes. It is used by [`CerednikDrinfeld.FormalODModule.eq_zero_of_nsmul_eq_zero_of_mem_eta`](thm.html#CerednikDrinfeld.FormalODModule.eq_zero_of_nsmul_eq_zero_of_mem_eta).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_nsmul_eq_zero_of_mem_eta_of_isReduced.lean

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

theorem CerednikDrinfeld.FormalODModule.eq_zero_of_nsmul_eq_zero_of_mem_eta_of_isReduced
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] [IsReduced S] [IsNoetherianRing S] (hp0 : ((p : ℕ) : S) = 0)
    (j : Zp2 p →+* S) (X : FormalODModule p S)
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (ζ : (X.toGradedCartierModuleData j hc).NMod)
    (hζ : ζ ∈ (X.toGradedCartierModuleData j hc).eta L hL.isCartierLMap.map_verschiebung)
    (hp : p • ζ = 0) :
    ζ = 0 := by sorry
