-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isIsomorphic_of_isIsomorphic_of_lieZero_le_ker
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isIsomorphic_of_isIsomorphic_of_lieZero_le_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/89e35328-cf7a-51f3-ae25-d4be7e28e8c3
-- title:
--   Isomorphic Drinfeld quadruples force isomorphic rigidified triples
-- statement:
--   Let $p$ be a prime and $k$ an algebraically closed field of characteristic $p$, let $\iota\colon W(\mathbb F_{p^2})\to W(k)$ be a ring homomorphism, write $\bar\iota$ for its composite with the quotient map $W(k)\to W(k)/pW(k)$, and let $\Phi$ be a formal $\mathcal O_D$-module of dimension $2$ over $W(k)/pW(k)$ (a commutative formal group law in two variables with an action of $W(\mathbb F_{p^2})$ and an endomorphism $\varpi$ with $\varpi^2=[p]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$). Assume: $\Phi$ is special for $\bar\iota$, i.e. $\mathrm{Lie}_0=\bigcap_a\ker(\mathrm{Lie}[a]-\bar\iota(a))$ and $\mathrm{Lie}_1=\bigcap_a\ker(\mathrm{Lie}[a]-\bar\iota(\sigma a))$ are complementary invertible modules; the kernel of $[p]$ on $\Phi$ has degree $p^4$; the index $0$ is critical, $\mathrm{Lie}_0\subseteq\ker\mathrm{Lie}(\varpi)$; the $0$- and $1$-eigenpieces of the Teichmüller action on the Cartier module of $\Phi$ are complementary ($h_{c\Phi}$); and $r_\Phi\colon(\mathbb Z_p^2,+)\to N$ is an additive map into the $N$-module of the resulting graded Cartier data which, for every canonical $L$-map $L$, maps $\mathbb Z_p^2$ bijectively onto the degree-$0$ $\eta$-piece of $L$. Let $B$ be a Noetherian commutative $\mathbb Z_p$-algebra with $p$ nilpotent, $\psi\colon W(k)\to B$ a ring homomorphism, and $t,t'$ rigidified triples $(X,n,\rho)$ over $B$ that are admissible for $(\iota,\psi)$: $X$ is special, has height $4$, and $\rho$ is an isogeny $\Phi\otimes_\psi B/pB\to X\bmod p$ of height $4n$. Let $Q,Q'$ be Drinfeld data over $B$ for $K=\mathbb Q_p$, $\mathcal O=\mathbb Z_p$, $\pi=p$ (pairs of full lattice functions on $\mathrm{Spec}\,B$ with invertible modules $T_0,T_1$, maps $\Pi_0,\Pi_1$ and comparison maps $u_0,u_1$), and suppose $Q$ is a Cartier quadruple for $t$ and $Q'$ one for $t'$ (the conditions relating $T_i$ to the Lie pieces of $X$ and the lattices to $\eta$-sections of the graded Cartier data of $X$ over Zariski localisations, summarised here). If $Q$ and $Q'$ are isomorphic as Drinfeld data, then $t$ and $t'$ are isomorphic, i.e. there are mutually inverse $\mathcal O_D$-homomorphisms $u\colon X_t\to X_{t'}$, $v\colon X_{t'}\to X_t$ and an $m\in\mathbb N$ with $[p^{m+n'}]\circ(\bar u\circ\rho)=[p^{m+n}]\circ\rho'$ on $X_{t'}\bmod p$.
--
--   This is the injectivity half of Drinfeld's classification of special formal $\mathcal O_D$-modules by lattice data: non-isomorphic admissible rigidified triples have non-isomorphic quadruples. It is used in the construction of the equivalence between admissible rigidified triples over Noetherian bases and Drinfeld data, the source of the $p$-adic uniformisation of Shimura curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_isIsomorphic_of_isIsomorphic_of_lieZero_le_ker.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isIsomorphic_of_isIsomorphic_of_lieZero_le_ker
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
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
    (t t' : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) (ht' : t'.IsAdmissible ι ψ)
    (Q Q' : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q) (hQ' : t'.IsCartierQuadruple ι hcΦ rΦ ψ Q')
    (hiso : Q.IsIsomorphic Q') :
    t.IsIsomorphic t' := by sorry
