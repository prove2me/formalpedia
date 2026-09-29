-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_ringHom_basis_forall_etaRed_iff_and_rigidNum_eq_nMk_mulVec_of_lieZero_le_ker_of_isAlgClosed_wittVector
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_ringHom_basis_forall_etaRed_iff_and_rigidNum_eq_nMk_mulVec_of_lieZero_le_ker_of_isAlgClosed_wittVector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/21c90cbe-e177-523f-9976-2e9145c7c1c3
-- title:
--   Coordinates for the reduced η-lattice and rigidification numerator
-- statement:
--   Fix a prime $p$ and write $\mathbb{W}_2 = W(\mathbb{F}_{p^2})$. Let $k$ be an algebraically closed field of characteristic $p$, let $\iota : \mathbb{W}_2 \to W(k)$ be a ring homomorphism, and let $\Phi$ be a formal $O_D$-module over $W(k)/pW(k)$ which is special for the reduction `jbar ι` of $\iota$, has height $4$ (its multiplication-by-$p$ has kernel of degree $p^4$), satisfies `lieZero` $\subseteq \ker$ `lieVarpi`, and whose graded pieces in degrees $0$ and $1$ of its Cartier module are complementary (`hcΦ`); let $\Phi$ be equipped with an additive map $r_\Phi : \mathbb{Z}_p^2 \to N$ of its associated graded Cartier data, such that a canonical $L$-map exists and such that for every canonical $L$-map $L$ the map $r_\Phi$ is a bijection of $\mathbb{Z}_p^2$ onto the degree-$0$ piece `etaPiece L … 0`. Let $B$ be an algebraically closed $\mathbb{Z}_p$-algebra in which $p$ is nilpotent, $\psi : W(k) \to B$ a ring homomorphism, and $t = (X,n,\rho)$ a rigidified datum over $B$ which is admissible for $(\iota,\psi)$: $X$ is special for $\psi\circ\iota$, has height $4$, and $\rho$ is an isogeny of height $4n$ from $\bar\Phi_\psi$ to $\bar X$. Work over the localisation $S$ of $B$ at the powers of $1$ and its reduction $\bar S = S/pS$, and assume the degree-$0$ and degree-$1$ graded pieces are complementary for $X_S$ (`hc`), for $\bar X_S$ (`hcb`) and for $\bar\Phi_{\psi,S}$ (`hcΦ1`); let $L$ be a canonical $L$-map on the graded Cartier data of $X_S$, and assume `lieZero` of $X$ is contained in $\ker$ `lieVarpi`. Then there exist a ring homomorphism $c : \mathbb{Z}_p \to W(\bar S)$, a pair $e_0, e_1$ of elements of the Cartier module of $\bar X_S$, and a matrix $\gamma \in M_2(\mathbb{Z}_p)$ such that: each $e_r$ lies in the degree-$0$ graded piece of $\bar X_S$ for `jSbar`; every element of that graded piece is $\sum_r w_r \cdot e_r$ for a unique $w : \mathrm{Fin}\,2 \to W(\bar S)$; an element $x$ of the $N$-module of $\bar X_S$ lies in the image under `etaRed` (the map induced by reduction modulo $p$) of the degree-$0$ piece `etaPiece L … 0` of $X_S$ if and only if $x =$ `nMk` $(\sum_r c(a_r)\cdot e_r, 0)$ for some $a \in \mathbb{Z}_p^2$; the map $a \mapsto$ `nMk` $(\sum_r c(a_r)\cdot e_r, 0)$ is injective on $\mathbb{Z}_p^2$; and the rigidification numerator `rigidNum`, the composite of $r_\Phi$ with the $N$-module maps induced by base change from $\Phi$ to $\bar\Phi_{\psi,S}$ and by $\bar\rho$, satisfies `rigidNum` $(w) =$ `nMk` $(\sum_r c((\gamma w)_r)\cdot e_r, 0)$ for all $w \in \mathbb{Z}_p^2$.
--
--   This is the coordinate form, on a geometric fibre, of Drinfeld's description of the reduced even $\eta$-lattice inside the $N$-module of a rigidified special formal module: both the reduced $\eta$-lattice and the image of the rigidification numerator are read in a single Witt-vector basis of the degree-$0$ Cartier piece, the former as the $c(\mathbb{Z}_p)$-span of the basis and the latter through a $2\times 2$ $p$-adic matrix. It is used to produce the determinant and $\eta$-section statement that governs the rigidification factor in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_ringHom_basis_forall_etaRed_iff_and_rigidNum_eq_nMk_mulVec_of_lieZero_le_ker_of_isAlgClosed_wittVector.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_ringHom_basis_forall_etaRed_iff_and_rigidNum_eq_nMk_mulVec_of_lieZero_le_ker_of_isAlgClosed_wittVector
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
    (hc : t.IsGradedS ι ψ (Rigidified.awayHom (1 : B))) (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom (1 : B)))
    (hcΦ1 : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom (1 : B)))
    (L : ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).M →+ ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).NMod)
    (hL : ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).IsCanonicalLMap L)
    (h0X : t.X.lieZero (structureMap ι ψ) ≤ LinearMap.ker t.X.lieVarpi) :
    ∃ (c : ℤ_[p] →+* WittVector p (Rigidified.Baway (1 : B) ⧸ pIdeal p (Rigidified.Baway (1 : B))))
      (e : Fin 2 → MvFormalGroup.CartierModule p (t.XbarS (Rigidified.awayHom (1 : B))).F)
      (γ : Matrix (Fin 2) (Fin 2) ℤ_[p]),
      (∀ r, e r ∈ (t.XbarS (Rigidified.awayHom (1 : B))).gradedPiece (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) 0) ∧
      (∀ m ∈ (t.XbarS (Rigidified.awayHom (1 : B))).gradedPiece (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) 0,
        ∃! w : Fin 2 → WittVector p (Rigidified.Baway (1 : B) ⧸ pIdeal p (Rigidified.Baway (1 : B))), m = ∑ r, w r • e r) ∧
      (∀ x : ((t.XbarS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) hcb).NMod,
        (∃ z ∈ ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).etaPiece L hL.isCartierLMap.map_verschiebung 0,
            t.etaRed ι ψ (Rigidified.awayHom (1 : B)) hc hcb z = x) ↔
          ∃ a : Fin 2 → ℤ_[p], x = ((t.XbarS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) hcb).nMk (∑ r, c (a r) • e r, 0)) ∧
      (∀ a a' : Fin 2 → ℤ_[p],
        ((t.XbarS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) hcb).nMk (∑ r, c (a r) • e r, 0) = ((t.XbarS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) hcb).nMk (∑ r, c (a' r) • e r, 0) → a = a') ∧
      (∀ w : Fin 2 → ℤ_[p],
        t.rigidNum ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom (1 : B)) hcb hcΦ1 w =
          ((t.XbarS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) hcb).nMk (∑ r, c ((γ.mulVec w) r) • e r, 0)) := by sorry
