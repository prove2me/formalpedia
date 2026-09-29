-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_bijOn_etaPiece_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_bijOn_etaPiece_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/1b8f74f1-9f16-5be1-8475-900f7f2e8005
-- title:
--   Additive bijections ℤₚ² → ηᵢ for rigidified special formal modules
-- statement:
--   Let $p$ be a prime and $k$ an algebraically closed field of characteristic $p$, let $\iota : W(\mathbb{F}_{p^2}) \to W(k)$ be a ring homomorphism, and let $\Phi$ be a formal $\mathcal{O}_D$-module of dimension $2$ over $W(k)/p$ — a commutative formal group law $F$ in two variables together with an action of $W(\mathbb{F}_{p^2})$ and a uniformiser endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ[a] = [\sigma a]\circ\varpi$. Assume, with respect to the homomorphism $j$ obtained from $\iota$ by reduction modulo $p$: $\Phi$ is special, i.e. its Lie algebra is the direct sum of the two eigenspaces `lieZero` and `lieOne`, both invertible modules; $\Phi$ has height $4$, i.e. the kernel of $[p]$ has degree $p^4$; the eigenspace `lieZero` is annihilated by the linear part of $\varpi$; and the degree $0$ and degree $1$ graded pieces of the Cartier module $C(\Phi)$ (the subgroups on which the Teichmüller action of $c \in \mathbb{F}_{p^2}$ agrees with the homothety by $j(c)^{p^n}$) are complementary, giving graded Cartier module data $D_\Phi$. Assume further that an additive map $r_\Phi : \mathbb{Z}_p^2 \to D_\Phi.\mathrm{NMod}$ is given which, for every canonical $L$-map $L$ on $D_\Phi$, maps $\mathbb{Z}_p^2$ bijectively onto `etaPiece` of $L$ in degree $0$, i.e. onto the intersection of the subgroup $\eta(L)$ of the quotient $\mathrm{NMod} = (M \times \Sigma)/\mathrm{nRel}$ with the image `nPiece 0` of the degree-$0$ part. Let $K$ be an algebraically closed field of characteristic $p$ which is a $\mathbb{Z}_p$-algebra, let $\psi' : W(k) \to K$ be a ring homomorphism, suppose $p$ is nilpotent in $K$, and let $t'$ be a rigidified object over $K$ (a formal $\mathcal{O}_D$-module $X$, an integer $n$, and a series $\rho$ over $K/p$) which is admissible for $\iota, \psi'$: $X$ is special for $\psi'\circ\iota$, of height $4$, and $\rho$ is an isogeny of height $4n$ from the reduction of $\Phi$ to $\bar X$. Assume the degree $0$ and degree $1$ graded pieces are complementary for $X$, for $\bar X$ and for the reduction of $\Phi$, all over the localisation of $K$ away from $1$, and let $L'$ be a canonical $L$-map for the resulting graded Cartier module data $D'$ of $X$. Then for each $i \in \{0,1\}$ there is an additive homomorphism $r : \mathbb{Z}_p^2 \to D'.\mathrm{NMod}$ mapping $\mathbb{Z}_p^2$ bijectively onto `etaPiece` of $L'$ in degree $i$.
--
--   This is the Cartier-module form of the statement that, on a geometric fibre, each graded piece $\eta_i$ of the unit-root part attached to a special formal $\mathcal{O}_D$-module of height $4$ carries a $\mathbb{Z}_p$-structure of rank $2$, as in the Čerednik–Drinfeld uniformisation of Shimura curves. It transports the degree-$0$ parametrisation assumed for the base object $\Phi$ over $W(k)/p$ to both degrees for an admissible rigidified object over an algebraically closed field, and is used in the construction of $\eta$-sections for such rigidified data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_bijOn_etaPiece_of_isAlgClosed.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_bijOn_etaPiece_of_isAlgClosed
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
    (hL' : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).IsCanonicalLMap L') :
    ∀ i : Fin 2, ∃ r : (Fin 2 → ℤ_[p]) →+ ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod,
      Set.BijOn r Set.univ (((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).etaPiece L' hL'.isCartierLMap.map_verschiebung i : Set _) := by sorry
