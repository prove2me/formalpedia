-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isQuadrupleOf_of_isPiTranslate
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isQuadrupleOf_of_isPiTranslate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/a9352c6d-93f0-5154-8b10-20d39c139362
-- title:
--   Pi-translates have the same Deligne datum
-- statement:
--   Fix a prime $p$ and an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota\colon W(\mathbb F_{p^2})\to W(k)$, and a formal $O_D$-module $\Phi$ of dimension $2$ over $W(k)/pW(k)$ which is special with respect to the reduction $\bar\jmath=\iota$ followed by $W(k)\to W(k)/pW(k)$ (its Lie algebra splits into complementary invertible weight-$0$ and weight-$1$ parts) and has height $4$, together with the hypothesis $hc_\Phi$ that the weight-$0$ and weight-$1$ graded pieces of the Cartier module of $\Phi$ are complementary, an additive map $r_\Phi\colon \mathbb Z_p^2\to$ the $N$-module of the graded Cartier module data attached to $\Phi$, and the hypothesis that for every canonical $L$-map $L$ on that data, $r_\Phi$ maps $\mathbb Z_p^2$ bijectively onto the degree-$0$ $\eta$-piece of $L$. Let $B$ be a Noetherian commutative $\mathbb Z_p$-algebra with $p$ nilpotent, $\psi\colon W(k)\to B$ a ring homomorphism, and let $t,t'$ be rigidified objects over $B$ (a formal $O_D$-module, an integer $n$, and a series $\rho$ over $B/pB$) with $t$ admissible for $(\iota,\psi)$ and $t'$ admissible for $(\iota,\psi\circ\sigma)$, $\sigma$ the Witt-vector Frobenius; admissibility means specialness, height $4$, and that $\rho$ is an isogeny of height $4n$ from the reduction of $\Phi$ to the reduction of $X$. Assume $t'$ is a $\Pi$-translate of $t$: the formal group laws and the $\varpi$-series agree, $t'.X.\mathrm{act}\,a=t.X.\mathrm{act}\,(\sigma a)$ for all $a$, and for some $c$ the rigidifications satisfy $[p^{c+t.n}]\circ(\rho'\circ(X_i\mapsto X_i^p))=[p^{c+t'.n}]\circ(\rho\circ\bar\varpi_\Phi)$. Let $Q,Q'$ be Drinfeld data over $B$ for $K=\mathbb Q_p$ and $\pi=p$, with $Q$ a Cartier quadruple for $t$ and $\psi$ and $Q'$ a Cartier quadruple for $t'$ and $\psi\circ\sigma$, and let $d$ be a Deligne datum over $B$. Then if $Q$ is a quadruple of $d$, so is $Q'$: for every prime $x$ of $B$ the pair of lattices $(Q'.L_0\,x,Q'.L_1\,x)$ is edge-nondegenerate for $d$ at $x$, and the kernels of $Q'.u_0\,x$ and $Q'.u_1\,x$ are the lines of the datum $d$ base-changed to the local ring at $x$ on the respective lattices.
--
--   This is the step in the Čerednik–Drinfeld comparison which shows that the Deligne datum (point of the formal upper half-plane functor) attached to a rigidified special formal module is unchanged when the module is replaced by its $\Pi$-translate, the twist by the Frobenius of the $W(\mathbb F_{p^2})$-structure. It feeds the statement that a $\Pi$-translate determines the same point, obtained by combining it with the uniqueness of the Deligne datum of a Drinfeld quadruple.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isQuadrupleOf_of_isPiTranslate.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isQuadrupleOf_of_isPiTranslate
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B))
    (t t' : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (ht' : t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)))
    (hπ : Rigidified.IsPiTranslate ψ t t')
    (Q Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q)
    (hQ' : t'.IsCartierQuadruple ι hcΦ rΦ (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) Q')
    (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (hd : Q.IsQuadrupleOf d) :
    Q'.IsQuadrupleOf d := by sorry
