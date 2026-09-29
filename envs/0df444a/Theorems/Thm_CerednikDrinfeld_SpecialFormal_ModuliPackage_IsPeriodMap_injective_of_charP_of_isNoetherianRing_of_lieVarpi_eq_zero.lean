-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_injective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.injective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/48e8c23e-aa6b-51a9-bce1-dbc2a6d64eed
-- title:
--   Injectivity of the period map on characteristic p points
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota : W(\mathbb{F}_{p^2}) \to W(k)$, and a formal $\mathcal{O}_D$-module $\Phi$ of dimension $2$ over $W(k)/pW(k)$ (a commutative formal group law in two variables with an action of $W(\mathbb{F}_{p^2})$ and an endomorphism $\varpi$ with $\varpi\circ\varpi = [p]$ and $\varpi\circ[a] = [\sigma a]\circ\varpi$). Assume: $\Phi$ is special for the reduction $\bar\jmath$ of $\iota$, i.e. the submodules $\mathrm{Lie}^0$ and $\mathrm{Lie}^1$ of its Lie module, cut out by $[a]$ acting as $\bar\jmath(a)$ resp. $\bar\jmath(\sigma a)$, are complementary and invertible; $\Phi$ has height $4$, i.e. the kernel algebra of $[p]$ on $\Phi$ is finite projective of fibre rank $p^4$; and the linear part of $\varpi$ annihilates $\mathrm{Lie}^0$. Let $M$ be a moduli package over $W(k)$ (a functor on rings $B$ equipped with $\psi : W(k)\to B$ and with $p$ nilpotent) which is a Zariski sheaf, and let $\eta$ attach to each rigidified object $t = (X,n,\rho)$ over $B$ a point of $M$, subject to: over Noetherian $B$, $\eta$ is injective on admissible $t$ exactly up to the isomorphism relation; $\eta$ commutes with base change along maps of Noetherian rings over $W(k)$; and every point of $M(B)$, $B$ Noetherian, comes Zariski-locally from an admissible rigidified object. Let $\bar\jmath$-graded pieces $0$ and $1$ of the Cartier module of $\Phi$ be complementary, witnessed by $h_{c\Phi}$, and let $r_\Phi : \mathbb{Z}_p^2 \to N$ be an additive map into the $N$-module of the associated graded Cartier module data which, for every canonical $L$-map $L$, maps $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ eta-piece of $L$. Finally let $\theta$ assign, to each Noetherian $\mathbb{Z}_p$-algebra $B$ with $\psi$ and $p$ nilpotent, a map from $M(B)$ to the set of Deligne data over $B$ for $\pi = p$, $K = \mathbb{Q}_p$, and assume $\theta$ is a period map in the sense of `IsPeriodMap`: Cartier quadruples for an admissible $t$ are quadruples of $\theta(\eta(t))$, and $\theta$ is compatible with base change of Deligne data. Then for every Noetherian $\mathbb{Z}_p$-algebra $B$, every $\psi : W(k) \to B$ and every witness that $p$ is nilpotent in $B$, if $p = 0$ in $B$ then $\theta_B$ is injective.
--
--   This is the characteristic-$p$ case of the injectivity half of the Čerednik–Drinfeld comparison: the period map from the moduli package of special formal $\mathcal{O}_D$-modules of height $4$ to Deligne data on the formal upper half plane is injective on Noetherian points killed by $p$. It is restricted to $p = 0$ so that it can be obtained from properness of the representing schemes over $k$ together with injectivity on $k$-points and on tangent vectors, without reconstructing rigidified objects from quadruples over a general base; it feeds the bijectivity statement over such bases and the local representability of the period map on affine opens.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_injective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero.lean

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

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.injective_of_charP_of_isNoetherianRing_of_lieVarpi_eq_zero
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
      (hB : IsNilpotent (p : B)), (p : B) = 0 → Function.Injective (θ B ψ hB)) := by sorry
