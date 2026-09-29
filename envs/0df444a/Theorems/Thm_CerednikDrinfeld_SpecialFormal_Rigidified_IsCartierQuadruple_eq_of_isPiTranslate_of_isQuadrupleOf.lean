-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_eq_of_isPiTranslate_of_isQuadrupleOf
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.eq_of_isPiTranslate_of_isQuadrupleOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/919ddf44-212f-50e9-8f49-6ff3d83f9f7a
-- title:
--   Pi-translation preserves the associated Deligne datum
-- statement:
--   Fix a prime $p$ and an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota \colon W(\mathbb F_{p^2}) \to W(k)$, and a formal $\mathcal O_D$-module $\Phi$ over $W(k)/pW(k)$ (a commutative two-dimensional formal group law with a $W(\mathbb F_{p^2})$-action and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ a = \sigma(a)\circ\varpi$). Assume: $\Phi$ is special for the structure map $\bar\jmath = \mathrm{pr}\circ\iota$, i.e. its weight-$0$ and weight-$1$ Lie parts are complementary and invertible; $\Phi$ has height $4$, i.e. $[p]$ has kernel of degree $p^4$; the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ are complementary, via `hcΦ`; and $r_\Phi \colon \mathbb Z_p^2 \to \mathrm{NMod}$ is an additive map which, for every canonical $L$-map $L$ on the resulting graded Cartier module data, maps the whole source bijectively onto `etaPiece L … 0`. Let $B$ be a Noetherian commutative $\mathbb Z_p$-algebra in which $p$ is nilpotent, $\psi \colon W(k) \to B$ a ring homomorphism, and let $t, t'$ be rigidified triples $(X, n, \rho)$ over $B$, with $t$ admissible for $(\iota,\psi)$ and $t'$ admissible for $(\iota,\psi\circ\sigma)$, where $\sigma$ is the Witt vector Frobenius: each $X$ is special of height $4$ and each $\rho$ is an isogeny of height $4n$ from the reduction of $\Phi$ to the reduction of $X$. Assume $t'$ is a $\Pi$-translate of $t$ over $\psi$: $t'.X$ and $t.X$ have the same formal group law and the same $\varpi$, $t'.X$'s action of $a$ is $t.X$'s action of $\sigma(a)$, and for some $c$ one has $[p^{c+t.n}]\circ t'.\rho\circ(X_i \mapsto X_i^p) = [p^{c+t'.n}]\circ t.\rho\circ\varpi_\Phi$ after reduction. Let $Q, Q'$ be Drinfeld data over $B$ for $(\mathbb Z_p, \mathbb Q_p, \pi = p)$ which are Cartier quadruples of $t$ (for $\psi$) and of $t'$ (for $\psi\circ\sigma$) respectively, with the same $\iota$, `hcΦ`, $r_\Phi$ — that is, $\rho$ is a homomorphism of formal $\mathcal O_D$-modules, the invertible modules $T_0, T_1$ are identified with the weight-$0$ and weight-$1$ Lie parts of $X$ compatibly with $\Pi_0, \Pi_1$ and the Lie action of $\varpi$, and, locally on $\mathrm{Spec}\,B$, the lattices $N_0, N_1$ and the maps $u_0, u_1$ are described by $\eta$-sections of the graded Cartier module of $X$ (these conditions are grouped here). Finally let $d, d'$ be Deligne data over $B$ with $Q$ a quadruple of $d$ and $Q'$ a quadruple of $d'$, in the sense that at each prime $x$ the edge nondegeneracy holds for $(Q.L_0 x, Q.L_1 x)$ and the kernels of $u_0 x$, $u_1 x$ are the lines of $d$ over the local ring at the corresponding lattices. Then $d' = d$.
--
--   This is the step of the Čerednik–Drinfeld comparison asserting that passing from a rigidified special formal $\mathcal O_D$-module to its $\Pi$-translate, with the $W(\mathbb F_{p^2})$-structure twisted by Frobenius, does not change the Deligne datum (lattice tree datum) attached to it through the Cartier-quadruple dictionary. It is used in the construction of the Drinfeld datum attached to an admissible rigidified triple and of the resulting isomorphism criterion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsCartierQuadruple_eq_of_isPiTranslate_of_isQuadrupleOf.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.eq_of_isPiTranslate_of_isQuadrupleOf
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
    (d d' : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (hd : Q.IsQuadrupleOf d) (hd' : Q'.IsQuadrupleOf d') :
    d' = d := by sorry
