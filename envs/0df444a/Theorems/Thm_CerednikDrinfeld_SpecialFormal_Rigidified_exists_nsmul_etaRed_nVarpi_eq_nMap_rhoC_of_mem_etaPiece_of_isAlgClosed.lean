-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_etaRed_nVarpi_eq_nMap_rhoC_of_mem_etaPiece_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_etaRed_nVarpi_eq_nMap_rhoC_of_mem_etaPiece_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/b2997a30-bc04-5f06-aa2b-9359bd8f3d9c
-- title:
--   Pointwise p-power comparison of η-pieces along ρ̄
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$ and a ring homomorphism $\iota : W(\mathbb{F}_{p^2}) \to W(k)$, and let $\Phi$ be a formal $O_D$-module of dimension $2$ over $W(k)/pW(k)$ (a commutative two-dimensional formal group law with an action of $W(\mathbb{F}_{p^2})$ and an endomorphism $\varpi$ with $\varpi^2 = [p]$). Assume: $\Phi$ is special for the reduction of $\iota$, i.e. its Lie algebra is the direct sum of the two eigenspaces $\mathrm{lieZero}$ and $\mathrm{lieOne}$, both invertible modules; $\Phi$ has height $4$, i.e. the kernel of $[p]$ has degree $p^4$; $\mathrm{lieZero} \subseteq \ker(\mathrm{lieVarpi})$; the graded pieces $0$ and $1$ of the Cartier module of $\Phi$ are complementary (`hcΦ`); and there is an additive map $r_\Phi : \mathbb{Z}_p^2 \to N(M_\Phi)$ which, for every canonical $L$-map $L$ on the graded Cartier data $M_\Phi$, maps the whole of $\mathbb{Z}_p^2$ bijectively onto $\mathrm{etaPiece}(L,0)$, the intersection of the subgroup `eta` attached to $L$ with the degree-$0$ part of $N(M_\Phi)$. Let further $K$ be an algebraically closed field of characteristic $p$ which is a $\mathbb{Z}_p$-algebra with $p$ nilpotent in $K$, let $\psi' : W(k) \to K$ be a ring homomorphism, and let $t' = (X, n, \rho)$ be a rigidified triple over $K$ which is admissible for $(\iota, \psi')$: $X$ is special for $\psi' \circ \iota$, has height $4$, and $\rho$ is an isogeny of height $4n$ from the base change of $\Phi$ to $K/pK$ to the reduction $\bar{X}$. Everything is read over the localisation of $K$ at the powers of $1$, through the structural map `awayHom`. Assume the graded pieces $0$ and $1$ are complementary for $X$ over that base (`hc`), for $\bar{X}$ (`hcb`) and for $\bar\Phi$ (`hcΦ1`), and let $L'$ be a canonical $L$-map on the graded Cartier data of $X$. Then for every canonical $L$-map $L_{\bar\Phi}$ on the graded Cartier data of $\bar\Phi$, every $i \in \{0,1\}$ and every $z$ in $\mathrm{etaPiece}(L', i)$, there are an integer $N \ge 0$ and an element $x$ of $\mathrm{etaPiece}(L_{\bar\Phi}, 0)$ with $$p^N \cdot \mathrm{etaRed}\big(\mathrm{nVarpi}^{\,i}(z)\big) = N(\bar\rho_*)(x),$$ where $\mathrm{etaRed}$ is the map of $N$-modules induced by reduction modulo $p$ from $N(M_X)$ to $N(M_{\bar X})$, and $N(\bar\rho_*)$ is the map $N(M_{\bar\Phi}) \to N(M_{\bar X})$ induced by the reduction of $\rho$ together with its compatibilities with the Verschiebung and with $\varpi$.
--
--   This is the cofinality input of the Čerednik–Drinfeld comparison: over an algebraically closed base every $\eta$-section of the Cartier $N$-module of the rigidified formal $O_D$-module $X$, twisted by a power of $\varpi$ and reduced modulo $p$, is the image under the isogeny $\bar\rho$ of an $\eta$-section of degree $0$ of the base point $\bar\Phi$, after multiplication by a power of $p$. It feeds the identification of the reduced $\eta$-sections of $X$ with the rigidification numerator, used by `exists_nsmul_etaRed_nVarpi_eq_rigidNum_of_mem_etaPiece_of_isAlgClosed`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_etaRed_nVarpi_eq_nMap_rhoC_of_mem_etaPiece_of_isAlgClosed.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_etaRed_nVarpi_eq_nMap_rhoC_of_mem_etaPiece_of_isAlgClosed
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
    ∀ (LΦ : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).M →+ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).NMod) (hLΦ : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).IsCanonicalLMap LΦ)
      (i : Fin 2) (z : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod), z ∈ ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).etaPiece L' hL'.isCartierLMap.map_verschiebung i →
      ∃ (N : ℕ) (x : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).NMod), x ∈ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).etaPiece LΦ hLΦ.isCartierLMap.map_verschiebung 0 ∧
        p ^ N • t'.etaRed ι ψ' (Rigidified.awayHom (1 : K)) hc hcb (((((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nVarpi : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod →ₗ[WittVector p (Rigidified.Baway (1 : K))] ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod) ^ (i : ℕ)) z) = ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (Rigidified.rhoC ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_verschiebungInt ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_endAct_varpiEnd ψ' t' ht'.2.2.1 (Rigidified.awayHom (1 : K))) x := by sorry
