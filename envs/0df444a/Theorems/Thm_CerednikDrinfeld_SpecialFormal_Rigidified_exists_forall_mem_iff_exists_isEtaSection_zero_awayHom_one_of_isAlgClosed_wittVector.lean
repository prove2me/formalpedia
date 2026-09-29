-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_mem_iff_exists_isEtaSection_zero_awayHom_one_of_isAlgClosed_wittVector
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_forall_mem_iff_exists_isEtaSection_zero_awayHom_one_of_isAlgClosed_wittVector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/7b7b5637-f407-5514-8266-9befb3fe9601
-- title:
--   Even η-lattice over a field read off one frame
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, and a ring homomorphism $\iota\colon W(\mathbf{F}_{p^2})\to W(k)$, where $W(\mathbf{F}_{p^2})$ is written `Zp2 p`. Let $\Phi$ be a formal $\mathcal{O}_D$-module over $W(k)/pW(k)$ (a two-dimensional commutative formal group law with an action of `Zp2 p` and an endomorphism $\varpi$ with $\varpi^2=[p]$) such that: $\Phi$ is special for the reduction $\bar\jmath=\iota \bmod p$, i.e. the weight-$0$ and weight-$1$ eigenspaces of the Lie algebra are complementary and invertible (`hΦ`); the kernel of $[p]$ on $\Phi$ has degree $p^4$ (`hΦ4`); the weight-$0$ Lie eigenspace is annihilated by the linear part of $\varpi$ (`h0Φ`); the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ are complementary (`hcΦ`), whence graded Cartier module data with its $N$-module. Let $r_\Phi\colon\mathbf{Z}_p^2\to N$ be additive, assume a canonical $L$-map for these data exists, and assume that for every canonical $L$-map $L$ the map $r_\Phi$ carries all of $\mathbf{Z}_p^2$ bijectively onto the degree-$0$ $\eta$-piece $\eta(L)\cap N_0$. Let $B$ be an algebraically closed field which is a $\mathbf{Z}_p$-algebra with $p$ nilpotent, $\psi\colon W(k)\to B$ a ring homomorphism, and $t=(X,n,\rho)$ a rigidified object over $B$ which is admissible for $(\iota,\psi)$: $X$ is special for $\psi\circ\iota$, has height $4$, and $\rho$ is an isogeny $\bar\Phi_\psi\to\bar X$ of height $4n$. Finally let $N_0$ assign to each point $x\in\operatorname{Spec}B$ a $\mathbf{Z}_p$-submodule of $\mathbf{Q}_p^2$, subject to the hypothesis that $v\in N_0(x)$ holds exactly when there are some $f\notin x$, some complementations `hc`, `hcb`, `hcΦf` of the degree-$0$ and degree-$1$ graded pieces of the Cartier modules of $X_{B_f}$, $\bar X_{B_f}$ and $\bar\Phi_{B_f}$ over the localisation $B_f=B[f^{-1}]$, some canonical $L$-map $L$ for $X_{B_f}$, and some $z$ with `IsEtaSection … 0 z v`, that is: $z$ lies in $\eta(L)$ intersected with the degree-$0$ piece of the $N$-module, and the image of $z$ under reduction to $\bar X_{B_f}$ is related to $v$ by the lattice relation with shift $n$ for the rigid numbering map built from $r_\Phi$, $\rho$ and base change, namely there are $m,\kappa\in\mathbf{N}$ and $w\in\mathbf{Z}_p^2$ with $p^m v=w$ and $p^{\kappa}\,r(w)=p^{\kappa+n+m}\,\bar z$. The conclusion is that one single frame suffices: there exist complementations `hc`, `hcb`, `hcΦ1` over the localisation at $1\in B$ and a canonical $L$-map $L$ for the graded Cartier module data of $X$ over that localisation such that for every $x\in\operatorname{Spec}B$ and every $v\in\mathbf{Q}_p^2$ one has $v\in N_0(x)$ if and only if there is a $z$ with `IsEtaSection … (awayHom 1) hc hcb hcΦ1 L hL 0 z v`.
--
--   In Drinfeld's description of the $p$-adic uniformisation of Shimura curves, the lattice attached to the even part of the $\eta$-filtration of a special formal $\mathcal{O}_D$-module is defined locally on the base; over a geometric fibre, where the base is a field and every basic open set is the whole space, the local presentations can be replaced by one fixed choice of gradings and canonical $L$-map. The result feeds the Cartier-quadruple statements that compute the $\eta$-lattice and its tangent line on a geometric fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_forall_mem_iff_exists_isEtaSection_zero_awayHom_one_of_isAlgClosed_wittVector.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_forall_mem_iff_exists_isEtaSection_zero_awayHom_one_of_isAlgClosed_wittVector
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k] (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
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
    {B : Type} [Field B] [IsAlgClosed B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (N₀ : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p]))
    (hN₀ : ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v) :
    ∃ (hc : t.IsGradedS ι ψ (Rigidified.awayHom (1 : B))) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom (1 : B)))
      (hcΦ1 : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (1 : B)))
      (L : ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).M →+ ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).NMod)
      (hL : ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).IsCanonicalLMap L),
      ∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]),
        v ∈ N₀ x ↔ ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom (1 : B)) hc hcb hcΦ1 L hL 0 z v := by sorry
