-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_ringHom_basis_forall_etaRed_nVarpi_iff_and_smul_rigidNum_eq_nMk_mulVec_of_lieOne_le_ker_of_isAlgClosed_wittVector
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_ringHom_basis_forall_etaRed_nVarpi_iff_and_smul_rigidNum_eq_nMk_mulVec_of_lieOne_le_ker_of_isAlgClosed_wittVector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/d43d5c8d-0bc5-50d6-9d45-f4d308045f23
-- title:
--   Coordinates for the degree-one η-lattice and p·rigidification numerator
-- statement:
--   Fix a prime $p$ and an algebraically closed field $k$ of characteristic $p$, a ring map $\iota : W(\mathbb{F}_{p^2}) \to W(k)$, and a formal $\mathcal{O}_D$-module $\Phi$ over $W(k)/pW(k)$ which is special for $\bar\jmath = (\mathrm{mod}\ p)\circ\iota$ (complementary, invertible Lie eigenpieces), has height $4$ (the kernel of multiplication by $p$ is of degree $p^4$), satisfies $\mathrm{lieZero}(\bar\jmath) \subseteq \ker(\mathrm{lieVarpi})$, and whose Cartier graded pieces in degrees $0,1$ (eigenspaces for the Teichmüller action, with eigencharacter $\bar\jmath(\cdot)^{p^n}$) are complementary, as witnessed by `hcΦ`. Let $r_\Phi : \mathbb{Z}_p^2 \to N(M_\Phi)$ be additive, assume a canonical $L$-map exists on the associated graded Cartier data, and assume $r_\Phi$ maps $\mathbb{Z}_p^2$ bijectively onto `etaPiece L _ 0` for every canonical $L$. Let $B$ be an algebraically closed $\mathbb{Z}_p$-algebra field with $p$ nilpotent, $\psi : W(k) \to B$, and $t = (X, n, \rho)$ a rigidified datum which is admissible for $(\iota,\psi)$: $X$ is special for $\psi\circ\iota$, has height $4$, and $\rho$ is an isogeny of height $4n$ from $\bar\Phi_\psi$ to $\bar X$. Work over $S = \mathrm{Baway}(1)$, the localisation of $B$ at the powers of $1$, with $\bar S = S/pS$; assume the degree $0,1$ pieces are complementary for $X_S$ (`hc`), for $\bar X_S$ (`hcb`) and for $\bar\Phi_S$ (`hcΦ1`), let $L$ be a canonical $L$-map on the Cartier data of $X_S$, and assume $\mathrm{lieOne}(\psi\circ\iota) \subseteq \ker(\mathrm{lieVarpi})$ for $X$. Then there are a ring homomorphism $c : \mathbb{Z}_p \to W(\bar S)$, elements $e_0,e_1$ of the Cartier module of $\bar X_S$ and a matrix $\gamma \in M_2(\mathbb{Z}_p)$ such that: each $e_r$ lies in the degree-$1$ graded piece for $\bar\jmath_{\bar S}$; every element of that piece is uniquely $\sum_r w_r e_r$ with $w \in W(\bar S)^2$; an element $x$ of $N(M_{\bar X_S})$ is of the form $\mathrm{etaRed}(\mathrm{nVarpi}\,z)$ for some $z$ in the degree-$1$ part `etaPiece L _ 1` if and only if $x = \mathrm{nMk}(\sum_r c(a_r)\,\varpi e_r, 0)$ for some $a \in \mathbb{Z}_p^2$; the map $a \mapsto \mathrm{nMk}(\sum_r c(a_r)\,\varpi e_r, 0)$ is injective on $\mathbb{Z}_p^2$; and for all $w \in \mathbb{Z}_p^2$, $p$ times the rigidification numerator $\mathrm{rigidNum}(w)$ — the composite of $r_\Phi$ with the $N$-functoriality maps along the base change $\Phi \to \bar\Phi_S$ and along $\rho$ — equals $\mathrm{nMk}(\sum_r c((\gamma w)_r)\,\varpi e_r, 0)$.
--
--   This is the odd-degree half of the coordinatisation step in the Čerednik–Drinfeld uniformisation: on a geometric fibre it writes both the reduction of $\varpi\cdot\eta_1$ and $p$ times the rigidification numerator in terms of a single Witt-vector basis of the degree-one part of the Cartier module of $\bar X_S$, with coefficients in the Frobenius-fixed copy $c(\mathbb{Z}_p) \subset W(\bar S)$. It feeds the determinant computation and the description of degree-one $\eta$-sections by a matrix equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_ringHom_basis_forall_etaRed_nVarpi_iff_and_smul_rigidNum_eq_nMk_mulVec_of_lieOne_le_ker_of_isAlgClosed_wittVector.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_ringHom_basis_forall_etaRed_nVarpi_iff_and_smul_rigidNum_eq_nMk_mulVec_of_lieOne_le_ker_of_isAlgClosed_wittVector
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
    (h1X : t.X.lieOne (structureMap ι ψ) ≤ LinearMap.ker t.X.lieVarpi) :
    ∃ (c : ℤ_[p] →+* WittVector p (Rigidified.Baway (1 : B) ⧸ pIdeal p (Rigidified.Baway (1 : B))))
      (e : Fin 2 → MvFormalGroup.CartierModule p (t.XbarS (Rigidified.awayHom (1 : B))).F)
      (γ : Matrix (Fin 2) (Fin 2) ℤ_[p]),
      (∀ r, e r ∈ (t.XbarS (Rigidified.awayHom (1 : B))).gradedPiece (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) 1) ∧
      (∀ m ∈ (t.XbarS (Rigidified.awayHom (1 : B))).gradedPiece (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) 1,
        ∃! w : Fin 2 → WittVector p (Rigidified.Baway (1 : B) ⧸ pIdeal p (Rigidified.Baway (1 : B))), m = ∑ r, w r • e r) ∧
      (∀ x : ((t.XbarS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) hcb).NMod,
        (∃ z ∈ ((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).etaPiece L hL.isCartierLMap.map_verschiebung 1,
            t.etaRed ι ψ (Rigidified.awayHom (1 : B)) hc hcb (((t.XS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jS ι ψ (Rigidified.awayHom (1 : B))) hc).nVarpi z) = x) ↔
          ∃ a : Fin 2 → ℤ_[p], x = ((t.XbarS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) hcb).nMk (∑ r, c (a r) • (t.XbarS (Rigidified.awayHom (1 : B))).varpiLinear (e r), 0)) ∧
      (∀ a a' : Fin 2 → ℤ_[p],
        ((t.XbarS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) hcb).nMk (∑ r, c (a r) • (t.XbarS (Rigidified.awayHom (1 : B))).varpiLinear (e r), 0) = ((t.XbarS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) hcb).nMk (∑ r, c (a' r) • (t.XbarS (Rigidified.awayHom (1 : B))).varpiLinear (e r), 0) → a = a') ∧
      (∀ w : Fin 2 → ℤ_[p],
        p • t.rigidNum ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom (1 : B)) hcb hcΦ1 w =
          ((t.XbarS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) hcb).nMk (∑ r, c ((γ.mulVec w) r) • (t.XbarS (Rigidified.awayHom (1 : B))).varpiLinear (e r), 0)) := by sorry
