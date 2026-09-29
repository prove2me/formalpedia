-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_pow_smul_of_isAdmissible
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_pow_smul_of_isAdmissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/88e0fe8a-0f95-5f38-baf9-bc17881d0c7f
-- title:
--   Every pⁿ⁺¹w is realised by a section of ηᵢ
-- statement:
--   Fix a prime $p$ and write $\mathbb{Z}_{p^2}$ for the Witt vectors of $\mathbb{F}_{p^2}$. Let $O$ be a commutative ring with a ring homomorphism $\iota:\mathbb{Z}_{p^2}\to O$, and let $\Phi$ be a formal $O_D$-module of dimension $2$ over $O/pO$, taken to be special for the reduction $\bar\jmath=\iota$ followed by $O\to O/pO$ (its Lie algebra is the direct sum of the complementary invertible submodules $\mathrm{lieZero}$ and $\mathrm{lieOne}$), of height $4$ (the kernel of multiplication by $p$ has degree $p^4$), with $\mathrm{lieZero}$ annihilated by the linear part of $\varpi$, and such that the graded pieces of degrees $0$ and $1$ of the Cartier module of $\Phi$ are complementary; call $D_\Phi$ the resulting graded Cartier module data. Let $r_\Phi:\mathbb{Z}_p^2\to N(D_\Phi)$ be additive, assume a canonical $L$-map for $D_\Phi$ exists, and assume that for every canonical $L$-map $L_\Phi$ the map $r_\Phi$ is a bijection of $\mathbb{Z}_p^2$ onto the degree-$0$ $\eta$-piece $\eta(L_\Phi)\cap N(D_\Phi)_0$. Let $B$ be a Noetherian $\mathbb{Z}_p$-algebra with $p$ nilpotent, $\psi:O\to B$ a ring homomorphism, and $t=(X,n,\rho)$ a rigidified object over $B$ which is admissible for $(\iota,\psi)$: $X$ is special for $\psi\circ\iota$, of height $4$, and $\rho$ is an isogeny $\bar\Phi_\psi\to\bar X$ of height $4n$. Let $i\in\{0,1\}$, let $g:B\to S$ be a ring homomorphism into a $\mathbb{Z}_p$-algebra $S$ with $p$ nilpotent, assume the degree-$0$ and degree-$1$ graded pieces are complementary for $X_S$, for $\bar X_S$ and for $\bar\Phi_S$, let $L$ be a canonical $L$-map for the graded Cartier module data of $X_S$, and let $w\in\mathbb{Z}_p^2$. Then there is $z$ in the $N$-module of $X_S$ satisfying the $\eta$-section condition of degree $i$ for the vector $p^{n+1}w\in\mathbb{Q}_p^2$: namely $z$ lies in $\eta(L)\cap N_i$, and the reduction of $\varpi_N^{\,i}z$ to the $N$-module of $\bar X_S$ is related to $p^{i}\cdot p^{n+1}w$ by the lattice relation for the rigidifying map built from $r_\Phi$, $\rho$ and base change, with offset $n$.
--
--   This is the existence half of the statement that, over each framed chart, the rigidified coordinates $p^{n+1}w$ with $w\in\mathbb{Z}_p^2$ are attained by sections of the graded $\eta$-pieces, as in Boutot–Carayol's treatment of the Čerednik–Drinfeld uniformisation. It is used by [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_mem_of_isAdmissible`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_mem_of_isAdmissible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isEtaSection_pow_smul_of_isAdmissible.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isEtaSection_pow_smul_of_isAdmissible
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero (Rigidified.jbar ι) ≤ LinearMap.ker Φ.lieVarpi)
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
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (i : Fin 2) {S : Type} [CommRing S] [Algebra ℤ_[p] S] (g : B →+* S) (hS : IsNilpotent (p : S))
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (L : _) (hL : ((t.XS g).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (w : Fin 2 → ℤ_[p]) :
    ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 g hc hcb hcΦg L hL i z
      ((p : ℚ_[p]) ^ (t.n + 1) • fun j => ((w j : ℤ_[p]) : ℚ_[p])) := by sorry
