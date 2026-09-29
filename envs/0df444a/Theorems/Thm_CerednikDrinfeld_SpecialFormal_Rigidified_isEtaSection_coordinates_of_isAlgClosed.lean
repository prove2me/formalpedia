-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_coordinates_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_coordinates_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/be1a3e58-b66b-518a-aaff-863d940682eb
-- title:
--   Rigidified ℚₚ-coordinates on the η-pieces over algebraically closed fields
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring map $\iota : \mathbb{W}(p,\mathbb{F}_{p^2}) \to \mathbb{W}(p,k)$, and a formal $O_D$-module $\Phi$ over $\mathbb{W}(p,k)/p\mathbb{W}(p,k)$ such that: $\Phi$ is special for the induced map $\bar\iota$ to the quotient (its zero and one Lie eigenspaces are complementary and invertible), $\Phi$ has height $4$, the zero eigenspace is contained in the kernel of the linear part of $\varpi$ on the Lie module, and the graded pieces of degrees $0$ and $1$ of the Cartier module of $\Phi$ are complementary, as witnessed by `hcΦ`. Let $r_\Phi : \mathbb{Z}_p^2 \to$ `NMod` of the graded Cartier data of $\Phi$ be additive and such that, for every canonical $L$-map $L$ on that data, $r_\Phi$ is a bijection of $\mathbb{Z}_p^2$ onto the degree-$0$ $\eta$-piece $\eta(L)\cap N_0$. Let $K$ be an algebraically closed field of characteristic $p$ carrying a $\mathbb{Z}_p$-algebra structure, with $p$ nilpotent in $K$, let $\psi' : \mathbb{W}(p,k) \to K$ be a ring map, and let $t' = (X,n,\rho)$ be a rigidified triple over $K$ which is admissible for $\iota,\psi'$ (that is, $X$ is special and of height $4$ and $\rho$ is an isogeny $\bar\Phi_{\psi'} \to \bar X$ of height $4n$). Assume, at the localisation map of $K$ at the powers of $1$, the three complementarity conditions: for the graded pieces of $X$, of $\bar X$ and of the base-changed $\bar\Phi$. Let $L'$ be a canonical $L$-map for the graded Cartier data of $X$ over that localisation, and $i \in \{0,1\}$. Then three assertions hold for the predicate `IsEtaSection`, which says of $z$ and $v : \mathbb{Q}_p^2$ that $z$ lies in the $i$-th $\eta$-piece of $L'$ and that the reduction `etaRed` of $\varpi^i z$ and the vector $p^i v$ satisfy the lattice relation with respect to `rigidNum` and the integer $n$, namely $p^m\,(p^i v)$ is integral, equal to some $w \in \mathbb{Z}_p^2$, and $p^k\,\mathrm{rigidNum}(w) = p^{k+n+m}\,\mathrm{etaRed}(\varpi^i z)$ for some $m,k$. The assertions are: every element of the $i$-th $\eta$-piece of $L'$ admits such a coordinate vector $v$; for every $v : \mathbb{Q}_p^2$ there are $e \in \mathbb{N}$ and an element $z$ of the $N$-module with $z$ and $p^e v$ in the relation; and the vector $v$ attached to a given $z$ is unique.
--
--   This is the comparison, over an algebraically closed base, between the $\eta$-pieces of the Cartier module of a rigidified special formal $O_D$-module and the $p$-adic plane $\mathbb{Q}_p^2$: the rigidification $\rho$, being an isogeny of height $4n$, transports the lattice $r_\Phi(\mathbb{Z}_p^2)$ into a commensurable lattice in the $\eta$-piece, and the three clauses say that the resulting coordinate assignment is everywhere defined, has $p$-divisible image filling $\mathbb{Q}_p^2$, and is single-valued. It feeds the analysis of Cartier quadruples and of the fibres of the period morphism in the Čerednik–Drinfel'd uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isEtaSection_coordinates_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_coordinates_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [Algebra ℤ_[p] K] (ψ' : WittVector p k →+* K) (hK : IsNilpotent (p : K))
    (t' : Rigidified p Φ K) (ht' : t'.IsAdmissible ι ψ')
    (hc : t'.IsGradedS ι ψ' (Rigidified.awayHom (1 : K))) (hcb : t'.IsGradedSbar ι ψ' (Rigidified.awayHom (1 : K)))
    (hcΦ1 : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ' (Rigidified.awayHom (1 : K)))
    (L' : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).M →+
      ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod)
    (hL' : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).IsCanonicalLMap L')
    (i : Fin 2) :
    (∀ z, z ∈ ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).etaPiece L' hL'.isCartierLMap.map_verschiebung i → ∃ v : Fin 2 → ℚ_[p], t'.IsEtaSection ι hcΦ rΦ ψ' ht'.2.2.1 (Rigidified.awayHom (1 : K)) hc hcb hcΦ1 L' hL' i z v) ∧
    (∀ v : Fin 2 → ℚ_[p], ∃ (e : ℕ) (z : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod), t'.IsEtaSection ι hcΦ rΦ ψ' ht'.2.2.1 (Rigidified.awayHom (1 : K)) hc hcb hcΦ1 L' hL' i z ((p : ℚ_[p]) ^ e • v)) ∧
    (∀ (z : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod) (v v' : Fin 2 → ℚ_[p]), t'.IsEtaSection ι hcΦ rΦ ψ' ht'.2.2.1 (Rigidified.awayHom (1 : K)) hc hcb hcΦ1 L' hL' i z v → t'.IsEtaSection ι hcΦ rΦ ψ' ht'.2.2.1 (Rigidified.awayHom (1 : K)) hc hcb hcΦ1 L' hL' i z v' → v = v') := by sorry
