-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_addMonoidHom_bijOn_etaPiece_zero_of_isCanonicalLMap
-- name    : CerednikDrinfeld.FormalODModule.exists_addMonoidHom_bijOn_etaPiece_zero_of_isCanonicalLMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/4fba8809-bed8-5279-a0d9-552832405c1f
-- title:
--   Degree-zero η-piece additively bijective to ℤₚ²
-- statement:
--   Fix a prime $p$ and an algebraically closed field $k$ of characteristic $p$, together with a ring homomorphism $\iota \colon W(\mathbb{F}_{p^2}) \to W(k)$, where $W(\mathbb{F}_{p^2})$ denotes `Zp2 p`. Let $\Phi$ be a formal $\mathcal{O}_D$-module over $B = W(k)/pW(k)$, that is, a commutative two-dimensional formal group law $\Phi.F$ over $B$ with an action of $W(\mathbb{F}_{p^2})$ by endomorphism series and a uniformiser series $\varpi$ satisfying $\varpi \circ \varpi = [p]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$, and write $j$ for the composite of $\iota$ with the reduction $W(k) \to B$. Assume: $\Phi$ is special for $j$, i.e. the Lie pieces $\Phi.\mathrm{lieZero}\,j$ and $\Phi.\mathrm{lieOne}\,j$ are complementary and both invertible as $B$-modules; $\Phi$ has height $4$, i.e. the series $[p]$ has kernel of degree $p^4$; and the two graded pieces of the Cartier module $M = \mathrm{CartierModule}\,p\,\Phi.F$ in degrees $0$ and $1$ are complementary additive subgroups, where the degree-$n$ piece consists of those $f$ with $[c]_*f = j(\tau(c))^{p^n} f$ for all $c \in \mathbb{F}_{p^2}$ (Teichmüller lifts $\tau$, homothety on the right). Let $D$ be the resulting graded Cartier module data on $M$, with Frobenius, Verschiebung and the operator induced by $\varpi$, and let $L \colon M \to N(D)$ be an additive map into the quotient $N(D) = (M \times \Sigma_D)/\mathrm{nRel}$ which is a canonical $L$-map: a Cartier $L$-map which, after base change along a surjection from a ring with no $p$-torsion carrying special graded Cartier module data, comes from a Cartier $L$-map there. The conclusion is that there exists an additive homomorphism $r \colon \mathbb{Z}_p^{\,2} \to N(D)$ (source $\mathrm{Fin}\,2 \to \mathbb{Z}_p$) which maps the whole of $\mathbb{Z}_p^{\,2}$ bijectively onto the degree-$0$ $\eta$-piece of $L$, namely the intersection of $\eta(L)$ with the degree-$0$ piece of $N(D)$, the Verschiebung relation $L(Vx) = [(\varpi x, 0)]$ being the one contained in the Cartier $L$-map part of the hypothesis on $L$.
--
--   This records, in the form of an additive bijection rather than a $\mathbb{Z}_p$-module isomorphism (no $\mathbb{Z}_p$-structure being available on $N(D)$), the fact that for a special formal $\mathcal{O}_D$-module of height $4$ the invariants attached to $L$ in each graded degree form a free $\mathbb{Z}_p$-lattice of rank $2$; it is the degree-$0$ case. It is used to rigidify the base point in the Čerednik–Drinfeld uniformisation, feeding the version of the statement in which the canonical $L$-map is constructed rather than assumed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_addMonoidHom_bijOn_etaPiece_zero_of_isCanonicalLMap.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalODModule.exists_addMonoidHom_bijOn_etaPiece_zero_of_isCanonicalLMap
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod) (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L) :
    ∃ r : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
      Set.BijOn r Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _) := by sorry
