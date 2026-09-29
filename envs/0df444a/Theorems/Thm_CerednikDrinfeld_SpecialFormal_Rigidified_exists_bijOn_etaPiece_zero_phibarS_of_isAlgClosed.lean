-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_bijOn_etaPiece_zero_phibarS_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_bijOn_etaPiece_zero_phibarS_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/5cee6bd8-b903-5c2b-aa6c-2412f3e2bdbb
-- title:
--   A rank-two ℤₚ-frame for η₀ after base change
-- statement:
--   Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$ and $\iota : W(\mathbb{F}_{p^2}) \to W(k)$ a ring homomorphism. Let $\Phi$ be a two-dimensional formal $O_D$-module over $W(k)/pW(k)$ (an [`MvFormalGroup`](def/MvFormalGroup_BasicV2.html#L15) in two variables, commutative, with an action of $W(\mathbb{F}_{p^2})$ and an endomorphism $\varpi$ satisfying $\varpi^2 = [p]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$) which is special with respect to the reduction $\bar\iota$ of $\iota$, i.e. its Lie algebra splits as the direct sum of the $\bar\iota$-eigenspace and the $\bar\iota\sigma$-eigenspace, both invertible, and which has height $4$ in the sense that the kernel algebra of $[p]$ is finite projective of rank $p^4$ at every field-valued point. Assume the $\bar\iota$-eigenspace of the Lie algebra lies in the kernel of the linear part of $\varpi$; assume $hc_\Phi$, that the graded pieces of degree $0$ and $1$ of the Cartier module of $\Phi$ (the parts on which the Teichmüller action of $c \in \mathbb{F}_{p^2}$ acts by the homothety $\bar\iota(\tau(c))^{p^n}$) are complementary; and assume given an additive map $r_\Phi : \mathbb{Z}_p^2 \to N$ into the $N$-module of the resulting graded Cartier module datum which, for every canonical $L$-map $L$ on that datum, maps all of $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ piece $\eta_0(L)$ of the $\eta$-subgroup. Let further $K$ be an algebraically closed field of characteristic $p$ which is a $\mathbb{Z}_p$-algebra and in which $p$ is nilpotent, $\psi' : W(k) \to K$ a ring homomorphism, and $t'$ a rigidified object over $K$ (a formal $O_D$-module $X$ over $K$, an integer $n$, and a series $\rho$ over $K/pK$) which is admissible for $\iota, \psi'$: $X$ is special for $\psi' \circ \iota$, of height $4$, and $\rho$ is an isogeny of height $4n$ from the base change of $\Phi$ to the reduction of $X$. Write $g$ for the localisation map of $K$ at the powers of $1$, and assume the three complementarity hypotheses $hc$, $hcb$, $hc_{\Phi 1}$ for the graded pieces in degrees $0$ and $1$ of the Cartier modules of $X_S$, $\bar X_S$ and $\bar\Phi_S := (\Phi \otimes_{\psi'} K/pK) \otimes_g$, with respect to the corresponding structure maps $j_S$, $\bar j_S$, $j_{\Phi,S}$; finally let $L'$ be a canonical $L$-map on the datum attached to $X_S$. The conclusion is that for every canonical $L$-map $L_\Phi$ on the graded Cartier module datum of $\bar\Phi_S$ with respect to $j_{\Phi,S}$ there exists an additive homomorphism $r' : \mathbb{Z}_p^2 \to N$ into its $N$-module which maps all of $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ piece $\eta_0(L_\Phi)$, i.e. the intersection of the $\eta$-subgroup of $L_\Phi$ with the degree-$0$ part of the $N$-module.
--
--   This is the unit-root descent statement for the coefficient module after base change: the degree-zero part of the $\eta$-subgroup attached to a canonical $L$-map on the special formal $O_D$-module of height $4$ obtained from $\Phi$ over the localised base is parametrised bijectively by $\mathbb{Z}_p^2$, so that it is a $\mathbb{Z}_p$-lattice of rank two. It is used in the comparison of $\eta_0$ for the rigidified object with $\eta_0$ for the base-changed coefficient module, in the Čerednik–Drinfeld uniformisation input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_bijOn_etaPiece_zero_phibarS_of_isAlgClosed.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_bijOn_etaPiece_zero_phibarS_of_isAlgClosed
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
    ∀ (LΦ : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).M →+ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).NMod) (hLΦ : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).IsCanonicalLMap LΦ),
      ∃ r' : (Fin 2 → ℤ_[p]) →+ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).NMod,
        Set.BijOn r' Set.univ (((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).etaPiece LΦ hLΦ.isCartierLMap.map_verschiebung 0 : Set _) := by sorry
