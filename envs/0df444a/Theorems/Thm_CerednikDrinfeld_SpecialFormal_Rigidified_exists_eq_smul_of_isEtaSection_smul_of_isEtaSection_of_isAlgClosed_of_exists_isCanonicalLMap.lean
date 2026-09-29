-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_eq_smul_of_isEtaSection_smul_of_isEtaSection_of_isAlgClosed_of_exists_isCanonicalLMap
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_eq_smul_of_isEtaSection_smul_of_isEtaSection_of_isAlgClosed_of_exists_isCanonicalLMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/abf46ac0-d377-5295-906f-5247cdc45fe9
-- title:
--   Fibrewise p-divisibility of η-sections with coordinates pv
-- statement:
--   Let $p$ be a prime, $O$ a commutative ring, $\iota\colon W(\mathbb F_{p^2})\to O$ a ring map, and $\Phi$ a formal $\mathcal O_D$-module of dimension $2$ over $O/pO$. Assume: $\Phi$ is special for $\bar\iota$ (the reduction of $\iota$), i.e. its Lie algebra is the direct sum of the $\bar\iota$-eigenspace and the Frobenius-twisted eigenspace, both invertible modules; $\Phi$ has height $4$, i.e. the kernel of multiplication by $p$ has degree $p^4$; the graded pieces in degrees $0$ and $1$ of the Cartier module of $\Phi$ are complementary, so that graded Cartier module data $D_\Phi$ are defined; $r_\Phi\colon\mathbb Z_p^2\to N(D_\Phi)$ is an additive map; a canonical $L$-map for $D_\Phi$ exists; and for every canonical $L$-map $L$ of $D_\Phi$ the map $r_\Phi$ is a bijection of $\mathbb Z_p^2$ onto the degree-$0$ $\eta$-piece $\eta(L)\cap N(D_\Phi)_0$. Let $K$ be an algebraically closed field which is a $\mathbb Z_p$-algebra with $p$ nilpotent, $\psi\colon O\to K$ a ring map, and $t=(X,n,\rho)$ a rigidified triple over $K$ which is admissible for $(\iota,\psi)$: $X$ is special for $\psi\circ\iota$ and of height $4$, and $\rho$ is an isogeny of height $4n$ from $\Phi\otimes_{\psi} K/pK$ to $X\bmod p$. Fix $i\in\{0,1\}$ and $v\in\mathbb Q_p^2$. Let $f_1,f_2\in K$ be non-zero, and over each localisation $K_{f_j}$ assume the three complementarity conditions (for $X$, for its reduction, and for the base-changed $\Phi$) and a canonical $L$-map $L_j$. Suppose $z_1$ is an $\eta$-section of degree $i$ over $K_{f_1}$ with coordinate vector $p\,v$, and $z_2$ one over $K_{f_2}$ with coordinate vector $v$; here being such an $\eta$-section means lying in $\eta(L_j)\cap N_i$ and, after applying $\varpi^i$ and reducing modulo $p$, satisfying the lattice relation with the rigidifying map built from $r_\Phi$ and $\rho$ and the vector $p^i$ times the given coordinate vector, namely the existence of $m,k\in\mathbb N$ and $w\in\mathbb Z_p^2$ with $p^m$ times that vector equal to $w$ and $p^k r(w)=p^{k+n+m}$ times the reduction. The conclusion is that there is $y$ in the degree-$i$ $\eta$-piece $\eta(L_1)\cap N_i$ over $K_{f_1}$ with $z_1=p\,y$.
--
--   This is the fibrewise divisibility step in the Cartier-theoretic description of special formal $\mathcal O_D$-modules underlying the Čerednik–Drinfeld uniformisation: over a geometric fibre, an $\eta$-section whose rigidified coordinates are $p\,v$ is $p$ times an $\eta$-section, provided $v$ itself is realised by an $\eta$-section in some chart. It is used by [`CerednikDrinfeld.SpecialFormal.Rigidified.mem_of_smul_mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.mem_of_smul_mem_of_exists_isEtaSection_map_of_isAlgClosed_of_ker_eq), and rests on the injectivity of coordinates for $\eta$-sections together with base change of $\eta$-sections along $K_{f_2}\to K_{f_1}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_eq_smul_of_isEtaSection_smul_of_isEtaSection_of_isAlgClosed_of_exists_isCanonicalLMap.lean

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

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_eq_smul_of_isEtaSection_smul_of_isEtaSection_of_isAlgClosed_of_exists_isCanonicalLMap
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {K : Type} [Field K] [IsAlgClosed K] [Algebra ℤ_[p] K] (ψ : O →+* K)
    (hK : IsNilpotent (p : K))
    (t : Rigidified p Φ K) (ht : t.IsAdmissible ι ψ)
    (i : Fin 2) (v : Fin 2 → ℚ_[p])
    (f₁ : K) (hf₁ : f₁ ≠ 0) (hc₁ : t.IsGradedS ι ψ (Rigidified.awayHom f₁))
    (hcb₁ : t.IsGradedSbar ι ψ (Rigidified.awayHom f₁)) (hcΦ₁ : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f₁))
    (L₁ : ((t.XS (Rigidified.awayHom f₁)).toGradedCartierModuleData _ hc₁).M →+ ((t.XS (Rigidified.awayHom f₁)).toGradedCartierModuleData _ hc₁).NMod)
    (hL₁ : ((t.XS (Rigidified.awayHom f₁)).toGradedCartierModuleData _ hc₁).IsCanonicalLMap L₁)
    (z₁ : _) (hz₁ : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f₁) hc₁ hcb₁ hcΦ₁ L₁ hL₁ i z₁
      (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v))
    (f₂ : K) (hf₂ : f₂ ≠ 0) (hc₂ : t.IsGradedS ι ψ (Rigidified.awayHom f₂))
    (hcb₂ : t.IsGradedSbar ι ψ (Rigidified.awayHom f₂)) (hcΦ₂ : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f₂))
    (L₂ : ((t.XS (Rigidified.awayHom f₂)).toGradedCartierModuleData _ hc₂).M →+ ((t.XS (Rigidified.awayHom f₂)).toGradedCartierModuleData _ hc₂).NMod)
    (hL₂ : ((t.XS (Rigidified.awayHom f₂)).toGradedCartierModuleData _ hc₂).IsCanonicalLMap L₂)
    (z₂ : _) (hz₂ : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f₂) hc₂ hcb₂ hcΦ₂ L₂ hL₂ i z₂ v) :
    ∃ y ∈ ((t.XS (Rigidified.awayHom f₁)).toGradedCartierModuleData _ hc₁).etaPiece L₁ hL₁.isCartierLMap.map_verschiebung i,
      z₁ = p • y := by sorry
