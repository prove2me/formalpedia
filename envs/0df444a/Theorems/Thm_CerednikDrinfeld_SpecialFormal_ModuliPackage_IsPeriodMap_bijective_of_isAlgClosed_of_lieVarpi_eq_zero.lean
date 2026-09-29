-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_bijective_of_isAlgClosed_of_lieVarpi_eq_zero
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.bijective_of_isAlgClosed_of_lieVarpi_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/e5b0fce1-d7e8-52bb-8be9-e6106ab59cc1
-- title:
--   Bijectivity of the period map on algebraically closed points
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota\colon W(\mathbb{F}_{p^2})\to W(k)$ and a formal $O_D$-module $\Phi$ of dimension $2$ over $W(k)/pW(k)$, and write $\bar\jmath$ for $\iota$ followed by reduction modulo $p$. Assume: $\Phi$ is special for $\bar\jmath$, i.e. the submodules $\operatorname{Lie}_0$ and $\operatorname{Lie}_1$ (the intersections over $a$ of the kernels of $\operatorname{lieAct}(a)-\bar\jmath(a)$, respectively $\operatorname{lieAct}(a)-\bar\jmath(\sigma a)$) are complementary in $\operatorname{Lie}\Phi$ and both invertible; $\Phi$ has height $4$, i.e. the kernel of $[p]$ on $\Phi$ is finite projective with fibre degree $p^4$; and the operator $\operatorname{lieVarpi}$ induced by $\varpi$ annihilates $\operatorname{Lie}_0$. Let $M$ be a moduli package over $W(k)$ (a functor on rings $B$ with a map from $W(k)$ and $p$ nilpotent) which is a Zariski sheaf, and let $\eta$ assign to each rigidified $\Phi$-datum over $B$ a point of $M(B)$ such that, over noetherian bases, $\eta$ separates admissible data exactly up to isomorphism, commutes with base change, and every point of $M(B)$ lies, locally for a finite cover of $\operatorname{Spec}B$ by basic opens $D(f_i)$ with $(f_i)=B$, in the image of $\eta$ on admissible data. Assume the graded pieces of index $0$ and $1$ of the Cartier module of $\Phi$ are complementary, via $\mathrm{hc}\Phi$, and let $r_\Phi\colon \mathbb{Z}_p^2\to \mathcal N$ be an additive map onto the associated $N$-module which, for every canonical $L$-map $L$, maps $\mathbb{Z}_p^2$ bijectively onto the $\eta$-piece of $L$ in degree $0$. Finally let $\theta$ assign to each noetherian $\mathbb{Z}_p$-algebra $B$ with $p$ nilpotent and structure map from $W(k)$ a map from $M(B)$ to the set of Deligne data over $B$ for $\pi=p$ in $\mathbb{Z}_p\subset\mathbb{Q}_p$, and assume $\theta$ is a period map for these data: it sends $\eta$ of an admissible datum carrying a Cartier quadruple $Q$ to a Deligne datum of which $Q$ is a quadruple, and it commutes with base change along $\mathbb{Z}_p$-algebra maps. Then for every algebraically closed field $\kappa$ that is a $\mathbb{Z}_p$-algebra in which $p$ is nilpotent, and every ring homomorphism $\psi_\kappa\colon W(k)\to\kappa$, the map $\theta_\kappa\colon M(\kappa)\to \Omega(\kappa)$ is bijective.
--
--   This is the comparison of the two moduli problems at the level of points with values in algebraically closed fields: over such a base the moduli package of special formal $O_D$-modules and Drinfeld's functor of Deligne data have the same points, under Boutot–Carayol's hypothesis that the index $0$ is critical for $\Phi$. It is the base case from which the local statements about the period morphism (injectivity over noetherian bases of characteristic $p$, and the local lifting statement on affine opens) are derived.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_bijective_of_isAlgClosed_of_lieVarpi_eq_zero.lean

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

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.bijective_of_isAlgClosed_of_lieVarpi_eq_zero
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
    (∀ (κ : Type) [Field κ] [IsAlgClosed κ] [IsNoetherianRing κ] [Algebra ℤ_[p] κ] (ψκ : WittVector p k →+* κ)
    (hκ : IsNilpotent (p : κ)), Function.Bijective (θ κ ψκ hκ)) := by sorry
