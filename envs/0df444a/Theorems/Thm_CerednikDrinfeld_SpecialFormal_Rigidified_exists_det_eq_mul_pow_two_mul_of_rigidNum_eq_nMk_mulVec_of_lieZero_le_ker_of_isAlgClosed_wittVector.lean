-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_det_eq_mul_pow_two_mul_of_rigidNum_eq_nMk_mulVec_of_lieZero_le_ker_of_isAlgClosed_wittVector
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_det_eq_mul_pow_two_mul_of_rigidNum_eq_nMk_mulVec_of_lieZero_le_ker_of_isAlgClosed_wittVector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/0919bb8f-7168-5971-85f3-47c872a1cf34
-- title:
--   Rigidification matrix has determinant u p²ⁿ
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$ and a ring homomorphism $\iota\colon W(\mathbb F_{p^2})\to W(k)$, and let $\Phi$ be a formal $O_D$-module (a two-dimensional commutative formal group with an action of $W(\mathbb F_{p^2})$ and an endomorphism $\varpi$ with $\varpi^2=[p]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$) over $W(k)/pW(k)$, assumed special for $\bar\jmath=\iota$ followed by reduction (the Lie algebra splits as the sum of the invertible weight-$0$ and weight-$1$ eigenspaces), of height $4$, with $\mathrm{lieZero}(\bar\jmath)$ contained in the kernel of the linear part of $\varpi$, and with its weight-$0$ and weight-$1$ graded pieces of the Cartier module complementary (`hcΦ`). Let $r_\Phi\colon\mathbb Z_p^2\to N$ be additive into the $N$-module of the associated graded Cartier module data, assume a canonical $L$-map exists for that data, and assume $r_\Phi$ maps $\mathbb Z_p^2$ bijectively onto the degree-$0$ $\eta$-piece $\mathrm{etaPiece}\,L\,0$ for every canonical $L$. Let $B$ be an algebraically closed $\mathbb Z_p$-algebra field with $p$ nilpotent in $B$, $\psi\colon W(k)\to B$ a ring homomorphism, and $t=(X,n,\rho)$ a rigidified object over $B$ which is admissible for $(\iota,\psi)$: $X$ is special for $\psi\circ\iota$ and of height $4$, and $\rho$ is an isogeny $\bar\Phi_\psi\to\bar X$ of height $4n$. Over the localisation $B[1/1]$ assume the three complementarity conditions for the graded pieces of $X_S$, $\bar X_S$ and $\bar\Phi_S$, a canonical $L$-map $L$ for the data of $X_S$, and $\mathrm{lieZero}(\psi\circ\iota)\subseteq\ker$ of the linear part of $\varpi$ on $X$. Finally let $c\colon\mathbb Z_p\to W(\bar S)$ be a ring homomorphism, let $e_0,e_1$ lie in the degree-$0$ graded piece of the Cartier module of $\bar X_S$ and form a basis of it over $W(\bar S)$ (every element of that piece is uniquely $\sum_r w_r\cdot e_r$), and let $\gamma\in M_2(\mathbb Z_p)$ satisfy, for all $w\in\mathbb Z_p^2$, $\mathrm{rigidNum}(w)=\mathrm{nMk}\bigl(\sum_r c((\gamma w)_r)\cdot e_r,\,0\bigr)$, where $\mathrm{rigidNum}$ is $r_\Phi$ followed by the base-change map to the data of $\bar\Phi_S$ and then by the map induced by $\rho$. Then there is a unit $u\in\mathbb Z_p^\times$ with $\det\gamma=u\,p^{2n}$.
--
--   This is the index computation at the heart of the Čerednik–Drinfel'd description: reading the rigidification numerator of an admissible rigidified special formal module in a $W$-basis of the degree-$0$ part of the Cartier module of the reduction gives a matrix whose determinant has valuation exactly $2n$, reflecting the height $4n$ of the rigidifying isogeny. It feeds the combined statement that records both this determinant and the characterisation of degree-$0$ $\eta$-sections by the equation $\gamma w = \cdot$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_det_eq_mul_pow_two_mul_of_rigidNum_eq_nMk_mulVec_of_lieZero_le_ker_of_isAlgClosed_wittVector.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_det_eq_mul_pow_two_mul_of_rigidNum_eq_nMk_mulVec_of_lieZero_le_ker_of_isAlgClosed_wittVector
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
    (h0X : t.X.lieZero (structureMap ι ψ) ≤ LinearMap.ker t.X.lieVarpi)
    (c : ℤ_[p] →+* WittVector p (Rigidified.Baway (1 : B) ⧸ pIdeal p (Rigidified.Baway (1 : B))))
    (e : Fin 2 → MvFormalGroup.CartierModule p (t.XbarS (Rigidified.awayHom (1 : B))).F)
    (he : ∀ r, e r ∈ (t.XbarS (Rigidified.awayHom (1 : B))).gradedPiece (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) 0)
    (heb : ∀ m ∈ (t.XbarS (Rigidified.awayHom (1 : B))).gradedPiece (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) 0,
      ∃! w : Fin 2 → WittVector p (Rigidified.Baway (1 : B) ⧸ pIdeal p (Rigidified.Baway (1 : B))), m = ∑ r, w r • e r)
    (γ : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (hγ : ∀ w : Fin 2 → ℤ_[p],
      t.rigidNum ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom (1 : B)) hcb hcΦ1 w =
        ((t.XbarS (Rigidified.awayHom (1 : B))).toGradedCartierModuleData (Rigidified.jSbar ι ψ (Rigidified.awayHom (1 : B))) hcb).nMk (∑ r, c ((γ.mulVec w) r) • e r, 0)) :
    ∃ u : ℤ_[p]ˣ, γ.det = (u : ℤ_[p]) * (p : ℤ_[p]) ^ (2 * t.n) := by sorry
