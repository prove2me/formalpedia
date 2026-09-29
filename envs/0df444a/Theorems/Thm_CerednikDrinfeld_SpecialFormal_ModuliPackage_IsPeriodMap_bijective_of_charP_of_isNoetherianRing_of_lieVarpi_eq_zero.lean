-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_bijective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.bijective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/8c88fe03-80b7-50f4-9ce7-d3e20cc77cc2
-- title:
--   Bijectivity of the period map on p-torsion Noetherian algebras
-- statement:
--   Fix a prime $p$ and an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota\colon W(\mathbb F_{p^2})\to W(k)$, and a formal $\mathcal O_D$-module $\Phi$ over $W(k)/pW(k)$, i.e. a commutative two-dimensional formal group law with an action of $W(\mathbb F_{p^2})$ and an endomorphism $\varpi$ with $\varpi\circ\varpi=[p]$ and $\varpi\circ a=\sigma(a)\circ\varpi$. Write $\bar\iota$ for $\iota$ followed by reduction modulo $p$. Assume: $\Phi$ is special for $\bar\iota$ (its Lie algebra is the direct sum of the two eigenspaces $\mathrm{Lie}_0$, $\mathrm{Lie}_1$, both invertible modules); the kernel of $[p]$ on $\Phi$ has degree $p^4$; and the linear part of $\varpi$ annihilates $\mathrm{Lie}_0$. Let $M$ be a moduli package over $W(k)$ (a functor on rings $B$ equipped with $\psi\colon W(k)\to B$ and $p$ nilpotent), assumed to be a Zariski sheaf, and let $\eta$ attach to every rigidified object $t=(X,n,\rho)$ over $B$ a point of $M$, such that on Noetherian $B$: $\eta$ identifies admissible rigidified objects exactly up to isomorphism, commutes with base change along maps compatible with $\psi$, and every point of $M$ comes Zariski-locally, on a finite cover by localisations away from generators of the unit ideal, from an admissible object. Let $\mathrm{Lie}$-graded data be given by a complement $hc_\Phi$ of the two graded pieces of the Cartier module of $\Phi$, together with an additive map $r_\Phi\colon \mathbb Z_p^2\to N(\Phi)$ mapping $\mathbb Z_p^2$ bijectively onto the degree-$0$ eta piece for every canonical $L$-map. Finally let $\theta$ assign to every point of $M$ over a Noetherian $\mathbb Z_p$-algebra $B$ with $p$ nilpotent a Deligne datum over $B$ for $(\mathbb Z_p\subset\mathbb Q_p,\pi=p)$, and assume $\theta$ is a period map: it carries $\eta(t)$, for admissible $t$, to a Deligne datum of which every Cartier quadruple attached to $t$ is a quadruple, and it commutes with base change. The conclusion is that for every Noetherian $\mathbb Z_p$-algebra $B$ with structure map $\psi\colon W(k)\to B$, with $p$ nilpotent in $B$ and $p=0$ in $B$, the map $\theta_B\colon M(B,\psi)\to \Omega(B)$ is bijective.
--
--   This is Drinfeld's comparison theorem on the special fibre, in the form given by Boutot–Carayol: the period morphism from the moduli of special formal $\mathcal O_D$-modules to the Deligne functor of the formal upper half plane is an isomorphism on Noetherian algebras killed by $p$. It is the base case for the version without the hypothesis $p=0$, obtained by induction over nilpotent thickenings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_bijective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.bijective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
(h0 : ∀ m ∈ Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι), Φ.lieVarpi m = 0)
(M : ModuliPackage.{0, 0} p (WittVector p k)) (hM : M.IsZariskiSheaf)
(η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
Rigidified p Φ B → M.obj B ψ hB)
(hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
(t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
(η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
(∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
(hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
(hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
(∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
(hL : IsNilpotent (p : L)),
∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
η L ((algebraMap B L).comp ψ) hL t =
M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
(θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
M.obj B ψ hB → OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B)
(hθ : CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap p k ι Φ M η hcΦ rΦ θ)
    :
    (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B)), (p : B) = 0 → Function.Bijective (θ B ψ hB)) := by sorry
