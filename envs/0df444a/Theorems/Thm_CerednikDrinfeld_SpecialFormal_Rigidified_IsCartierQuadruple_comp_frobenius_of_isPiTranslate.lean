-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_comp_frobenius_of_isPiTranslate
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.comp_frobenius_of_isPiTranslate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/df8f241b-c35b-5ceb-8045-48d6df4e72b7
-- title:
--   Cartier quadruples transfer to Pi-translates
-- statement:
--   Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$, and $\iota \colon \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to W(k)$ a ring homomorphism; write $\bar\iota$ for $\iota$ followed by the quotient map $W(k) \to W(k)/pW(k)$. Let $\Phi$ be a formal $O_D$-module over $W(k)/pW(k)$ which is special for $\bar\iota$ (its Lie pieces $\mathrm{lieZero}$ and $\mathrm{lieOne}$ are complementary and each invertible) and of height $4$ (the kernel of the action of $p$ has degree $p^4$), such that the degree $0$ and degree $1$ graded pieces of its Cartier module are complementary, as recorded by `hcΦ`. Let $r_\Phi$ be an additive map $(\mathrm{Fin}\,2 \to \mathbb{Z}_p) \to N$, where $N$ is the $N$-module of the graded Cartier module data attached to $\Phi$, $\bar\iota$ and `hcΦ`, and assume $r_\Phi$ is a bijection of all of $\mathrm{Fin}\,2 \to \mathbb{Z}_p$ onto the degree $0$ eta piece $\mathrm{etaPiece}\,L\,0$ for every canonical $L$-map $L$. Let $B$ be a Noetherian commutative $\mathbb{Z}_p$-algebra with $p$ nilpotent, $\psi \colon W(k) \to B$ a ring homomorphism, and $\sigma$ the Frobenius of $W(k)$. Let $t = (X,n,\rho)$ and $t' = (X',n',\rho')$ be rigidified objects over $B$, with $t$ admissible for $(\iota,\psi)$ and $t'$ admissible for $(\iota,\psi\circ\sigma)$ (in each case: $X$ special for the structure map, of height $4$, and $\rho$ an isogeny of height $4n$ from the reduction of $\Phi$ along $\psi$ to $\bar X$), and assume $t'$ is a $\Pi$-translate of $t$ over $\psi$: $X'$ has the same formal group law and the same $\varpi$ as $X$, its $\mathbb{Z}_{p^2}$-action satisfies $X'.\mathrm{act}(a) = X.\mathrm{act}(\sigma a)$, and for some $c \in \mathbb{N}$ one has $[p^{c+n}]_{\bar X} \circ (\rho' \circ (X_i \mapsto X_i^p)) = [p^{c+n'}]_{\bar X} \circ (\rho \circ \varpi_\Phi)$ after reduction along $\psi$. Finally let $Q$ be a Drinfeld datum over $B$ for $\mathbb{Q}_p$ with uniformiser $p \in \mathbb{Z}_p$. Then, if $Q$ is a Cartier quadruple for $t$ relative to $\iota$, `hcΦ`, $r_\Phi$ and $\psi$ — that is, $\rho$ is an $O_D$-module homomorphism, there are $B$-linear isomorphisms of $Q.T_0$, $Q.T_1$ with the two Lie pieces of $X$ carrying $Q.\Pi_0$, $Q.\Pi_1$ to the map induced by $\varpi$, and at every prime of $B$ the lattices $Q.N_0$, $Q.N_1$ are described by eta sections over Zariski-local neighbourhoods compatibly with the maps $Q.u_0$, $Q.u_1$, these clauses being summarised here — then $Q$ is also a Cartier quadruple for $t'$ relative to $\iota$, `hcΦ`, $r_\Phi$ and the twisted structure map $\psi\circ\sigma$.
--
--   This is the one-quadruple form of the compatibility, in Boutot–Carayol's treatment of the Čerednik–Drinfeld uniformisation, between the $\Pi$-translation of a special formal $O_D$-module and the Frobenius twist of its structure map: passing from $t$ to a $\Pi$-translate $t'$ over $\psi\circ\sigma$ leaves the associated Drinfeld datum unchanged. It is used in [`CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isIsomorphic_quadruple_of_isPiTranslate`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.isIsomorphic_quadruple_of_isPiTranslate).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_comp_frobenius_of_isPiTranslate.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.comp_frobenius_of_isPiTranslate
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
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q) :
    t'.IsCartierQuadruple ι hcΦ rΦ (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) Q := by sorry
