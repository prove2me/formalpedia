-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsPeriodValue_isQuadrupleOf
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsPeriodValue.isQuadrupleOf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/9ac16300-bc94-597b-93ab-dcc3730d18c8
-- title:
--   Every Cartier quadruple realises a period value
-- statement:
--   Let $p$ be a prime and $k$ an algebraically closed field of characteristic $p$, let $\iota : \mathbb{W}(\mathbb{F}_{p^2}) \to W(k)$ be a ring homomorphism, and let $\Phi$ be a formal $O_D$-module of dimension $2$ over $W(k)/pW(k)$ which is special for the induced map $\bar\jmath = \iota$ followed by the quotient map (its $\mathrm{Lie}$ splits as the direct sum of the two eigenspace submodules `lieZero` and `lieOne`, each invertible) and has height $4$ (the kernel of the action of $p$ has degree $p^4$). Assume in addition: $\varpi$ annihilates `lieZero`; the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ for $\bar\jmath$ are complementary, via a witness $h_{c\Phi}$; and $r_\Phi$ is an additive map from $\mathbb{Z}_p^2$ to the $N$-module of the graded Cartier module data $\Phi$.`toGradedCartierModuleData` that, for every canonical $L$-map $L$, maps all of $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ eta-piece $\mathrm{eta}(L) \cap N_0$. Let $B$ be a noetherian commutative $\mathbb{Z}_p$-algebra with $p$ nilpotent, $\psi : W(k) \to B$ a ring homomorphism, and $t = (X, n, \rho)$ a rigidified object over $B$ that is admissible for $(\iota,\psi)$: $X$ is special for $\psi\circ\iota$ and of height $4$, and $\rho$ is an isogeny of height $4n$ from the reduction of $\Phi$ to the reduction of $X$. Let $d$ be a Deligne datum over $B$ for the uniformiser $p \in \mathbb{Z}_p$ inside $\mathbb{Q}_p$, and suppose $d$ is a period value of $t$, i.e. some Drinfeld datum $Q_0$ is a Cartier quadruple of $t$ with $Q_0$ the quadruple of $d$. Then every Drinfeld datum $Q$ that is a Cartier quadruple of $t$ is itself the quadruple of $d$: for each prime $x$ of $B$, the datum $d$ is edge-nondegenerate at $x$ for the lattice pair attached to $Q$ at $x$, and the kernels of $Q.u_0\,x$ and $Q.u_1\,x$ are exactly the lines cut out by the localisation of $d$ at those two lattices.
--
--   This converts the existential formulation of the period map for special formal $O_D$-modules into a universal one, as required when comparing the two specifications of the period map in the Čerednik–Drinfeld uniformisation. It is used in establishing the existence of a period map for the moduli package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsPeriodValue_isQuadrupleOf.lean

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
import Definitions.Def_CerednikDrinfeld_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsPeriodValue.isQuadrupleOf
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
    (h0 : ∀ m ∈ Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι), Φ.lieVarpi m = 0)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (d : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B) (hd : t.IsPeriodValue ι hcΦ rΦ ψ d)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (hQ : t.IsCartierQuadruple ι hcΦ rΦ ψ Q) :
    Q.IsQuadrupleOf d := by sorry
