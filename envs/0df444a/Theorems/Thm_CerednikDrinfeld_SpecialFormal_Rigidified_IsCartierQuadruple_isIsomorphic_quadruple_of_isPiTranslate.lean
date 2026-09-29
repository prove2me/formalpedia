-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isIsomorphic_quadruple_of_isPiTranslate
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isIsomorphic_quadruple_of_isPiTranslate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/6a712bbc-343a-5d98-a63b-4a7e78d936b5
-- title:
--   Cartier quadruples of a Pi-translate are isomorphic
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota\colon W(\mathbb F_{p^2})\to W(k)$ (here `Zp2 p` is $W(\mathbb F_{p^2})$), and a formal $O_D$-module $\Phi$ of dimension $2$ over $W(k)/pW(k)$ which is special for the reduction $\bar\iota$ of $\iota$ (the zero and one Lie eigenpieces are complementary and invertible) and of height $4$, i.e. the kernel of the action of $p$ has degree $p^4$. Assume the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ with respect to $\bar\iota$ are complementary, via a witness $hc_\Phi$, and let $r_\Phi$ be an additive map from $\mathbb Z_p^2$ to the $N$-module of the graded Cartier module data of $\Phi$ which, for every canonical $L$-map $L$ on that data, maps the whole of $\mathbb Z_p^2$ bijectively onto the degree-$0$ $\eta$-piece attached to $L$. Let $B$ be a Noetherian commutative $\mathbb Z_p$-algebra in which $p$ is nilpotent, and $\psi\colon W(k)\to B$ a ring homomorphism. Let $t=(X,n,\rho)$ and $t'=(X',n',\rho')$ be rigidified objects over $B$ (a formal $O_D$-module, a natural number, and a $2$-tuple of power series over $B/pB$), with $t$ admissible for $(\iota,\psi)$ and $t'$ admissible for $(\iota,\psi\circ\sigma)$, $\sigma$ the Witt-vector Frobenius of $W(k)$; admissibility means that the formal $O_D$-module is special, of height $4$, and that the rigidification is an isogeny of height $4n$ from the reduction of $\Phi$ to the reduction of the module. Assume $t'$ is a $\Pi$-translate of $t$ over $\psi$: the formal group laws and the uniformiser actions $\Pi$ of $X'$ and $X$ agree, the $W(\mathbb F_{p^2})$-action of $X'$ is that of $X$ precomposed with $\sigma$, and for some $c$ one has $[p^{c+n}]\circ\rho'\circ(X_i\mapsto X_i^p)=[p^{c+n'}]\circ\rho\circ\bar\Pi_\Phi$ on the reductions. Finally let $Q,Q'$ be Drinfeld data over $B$ for the field $\mathbb Q_p$ and the uniformiser $p\in\mathbb Z_p$ — families of full lattices $N_0(x)\le N_1(x)$ in $\mathbb Q_p^2$ indexed by $\operatorname{Spec} B$ with $pN_1(x)\subseteq N_0(x)$ and open membership loci, invertible $B$-modules $T_0,T_1$ with maps $\Pi_0,\Pi_1$ whose composites are multiplication by $p$, and comparison maps $u_0,u_1$ from the base-changed lattices to the stalks of $T_0,T_1$ — and suppose $Q$ is a Cartier quadruple for $t$ over $\psi$ and $Q'$ is a Cartier quadruple for $t'$ over $\psi\circ\sigma$, both with respect to the same $\iota$, $hc_\Phi$, $r_\Phi$; being a Cartier quadruple means that $\rho$ is an $O_D$-module homomorphism, that $T_0,T_1$ are identified $B$-linearly with the zero and one Lie eigenpieces of $X$ compatibly with $\Pi$ and the linear part of $\Pi$ on the Lie module, and that over each point of $\operatorname{Spec} B$ the lattices $N_i(x)$ and the maps $u_i$ are described by the $\eta$-sections of the graded Cartier module of $X$ over localisations $B_f$. The conclusion is that $Q$ and $Q'$ are isomorphic as Drinfeld data.
--
--   This is the statement that the Drinfeld datum attached to an admissible rigidified special formal $O_D$-module is unchanged, up to isomorphism of data, when one passes to a $\Pi$-translate together with the Frobenius twist of the structure morphism — no shift of the lattice degrees occurs under this double twist. It is used in the construction of the Drinfeld datum of a $\Pi$-translate point, and thence in the descent step of the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isIsomorphic_quadruple_of_isPiTranslate.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isIsomorphic_quadruple_of_isPiTranslate
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
    (hQ' : t'.IsCartierQuadruple ι hcΦ rΦ (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) Q') :
    Q.IsIsomorphic Q' := by sorry
