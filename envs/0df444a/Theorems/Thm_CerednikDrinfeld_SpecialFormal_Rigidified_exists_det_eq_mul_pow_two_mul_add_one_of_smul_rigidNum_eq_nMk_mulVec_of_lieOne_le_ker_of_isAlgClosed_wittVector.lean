-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_det_eq_mul_pow_two_mul_add_one_of_smul_rigidNum_eq_nMk_mulVec_of_lieOne_le_ker_of_isAlgClosed_wittVector
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_det_eq_mul_pow_two_mul_add_one_of_smul_rigidNum_eq_nMk_mulVec_of_lieOne_le_ker_of_isAlgClosed_wittVector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/dd29c2d7-339d-5ad9-9e5b-ee0e43f7f5a8
-- title:
--   Determinant u p²ⁿ⁺¹ for the rigidification numerator matrix
-- statement:
--   Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$, and $\iota : W(\mathbb{F}_{p^2}) \to W(k)$ a ring homomorphism, writing $\bar{\jmath}(\iota)$ for $\iota$ followed by reduction modulo $p$. Let $\Phi$ be a formal $O_D$-module of dimension $2$ over $W(k)/pW(k)$ which is special for $\bar{\jmath}(\iota)$ (the zero and one eigenspaces of the $W(\mathbb{F}_{p^2})$-action on the Lie algebra are complementary and invertible), whose multiplication by $p$ has kernel of degree $p^4$, whose zero eigenspace lies in the kernel of the map induced by $\varpi$ on the Lie algebra, and whose Cartier module graded pieces in degrees $0$ and $1$ (the eigenspaces for Teichmüller lifts, with eigenvalue raised to $p^n$) are complementary, this last by `hcΦ`. Let $r_\Phi : \mathbb{Z}_p^2 \to N$ be an additive map into the $N$-module of the graded Cartier module data of $\Phi$, assume a canonical $L$-map for that data exists, and assume that $r_\Phi$ maps $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ $\eta$-piece `etaPiece L hL.isCartierLMap.map_verschiebung 0` for every canonical $L$-map $L$. Let $B$ be an algebraically closed field which is a $\mathbb{Z}_p$-algebra with $p$ nilpotent, $\psi : W(k) \to B$ a ring homomorphism, and $t$ a rigidified datum over $B$, consisting of a formal $O_D$-module $X$ over $B$, an integer $n$ and a series $\rho$ over $B/p$, which is admissible for $(\iota,\psi)$: $X$ is special for $\psi \circ \iota$, multiplication by $p$ on $X$ has kernel of degree $p^4$, and $\rho$ is an isogeny of height $4n$ from the reduction of $\Phi$ along $\psi$ to $\bar X$. Work over the localisation `Rigidified.Baway (1 : B)` of $B$ at the powers of $1$, with structure map `Rigidified.awayHom (1 : B)`; assume the degree-$0$ and degree-$1$ graded pieces are complementary for $X_S$, for $\bar X_S$ and for $\bar\Phi_S$ (hypotheses `hc`, `hcb`, `hcΦ1`), fix a canonical $L$-map $L$ for the graded Cartier module data of $X_S$, and assume the one eigenspace of the Lie algebra of $X$ lies in the kernel of the map induced by $\varpi$. Let $c : \mathbb{Z}_p \to W(\mathrm{Baway}(1)/p)$ be a ring homomorphism, and let $e_0,e_1$ be elements of the Cartier module of $\bar X_S$ lying in the degree-$1$ graded piece and forming a basis of it, in the sense that every element of that piece is uniquely of the form $\sum_r w_r \cdot e_r$ with $w \in W(\mathrm{Baway}(1)/p)^2$. Finally let $\gamma$ be a $2 \times 2$ matrix over $\mathbb{Z}_p$ such that, for every $w \in \mathbb{Z}_p^2$, $p$ times the rigidification numerator `t.rigidNum` of $w$ — the composite of $r_\Phi$ with the base-change map of $\Phi$ to $\bar\Phi_S$ and with the map induced by $\rho$ — equals the class `nMk` of the pair $\bigl(\sum_r c((\gamma w)_r) \cdot \varpi(e_r),\, 0\bigr)$. Then there is a unit $u \in \mathbb{Z}_p^\times$ with $\det \gamma = u\,p^{2n+1}$.
--
--   This is the odd-exponent determinant computation in the Čerednik–Drinfeld theory of special formal $O_D$-modules: the matrix reading $p$ times the rigidification numerator against the $\varpi$-image of a basis of the degree-$1$ part of the Cartier module of $\bar X_S$ has determinant of valuation exactly $2n+1$, the extra one coming from the single application of $\varpi$. It is used in the chart-level comparison which identifies the $\eta$-sections of a rigidified special formal module with lattice data, via [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_det_eq_and_forall_exists_isEtaSection_one_iff_mulVec_eq_of_lieOne_le_ker_of_isAlgClosed_wittVector`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_det_eq_and_forall_exists_isEtaSection_one_iff_mulVec_eq_of_lieOne_le_ker_of_isAlgClosed_wittVector).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_det_eq_mul_pow_two_mul_add_one_of_smul_rigidNum_eq_nMk_mulVec_of_lieOne_le_ker_of_isAlgClosed_wittVector.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_det_eq_mul_pow_two_mul_add_one_of_smul_rigidNum_eq_nMk_mulVec_of_lieOne_le_ker_of_isAlgClosed_wittVector
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
    (h1X : t.X.lieOne (structureMap ι ψ) ≤ LinearMap.ker t.X.lieVarpi)
    (c : ℤ_[p] →+* WittVector p (Rigidified.Baway (1 : B) ⧸ pIdeal p (Rigidified.Baway (1 : B))))
    (e : Fin 2 → MvFormalGroup.CartierModule p (t.XbarS (Rigidified.awayHom (1 : B))).F)
    (he : ∀ r, e r ∈ (t.XbarS (Rigidified.awayHom (1 : B))).gradedPiece (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) 1)
    (heb : ∀ m ∈ (t.XbarS (Rigidified.awayHom (1 : B))).gradedPiece (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) 1,
      ∃! w : Fin 2 → WittVector p (Rigidified.Baway (1 : B) ⧸ pIdeal p (Rigidified.Baway (1 : B))), m = ∑ r, w r • e r)
    (γ : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (hγ : ∀ w : Fin 2 → ℤ_[p],
      p • t.rigidNum ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom (1 : B)) hcb hcΦ1 w =
        ((t.XbarS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) hcb).nMk (∑ r, c ((γ.mulVec w) r) • (t.XbarS (Rigidified.awayHom (1 : B))).varpiLinear (e r), 0)) :
    ∃ u : ℤ_[p]ˣ, γ.det = (u : ℤ_[p]) * (p : ℤ_[p]) ^ (2 * t.n + 1) := by sorry
