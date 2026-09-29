-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_exists_cover_exists_map_eq_map_of_isBaseChange_of_ker_mul_ker_eq_bot_of_lieVarpi_eq_zero
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.exists_cover_exists_map_eq_map_of_isBaseChange_of_ker_mul_ker_eq_bot_of_lieVarpi_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/b60fffb2-d461-52ac-a059-e4e30eed24c2
-- title:
--   Zariski-local lifting of moduli points along square-zero thickenings
-- statement:
--   Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$, and $\iota : W(\mathbb F_{p^2}) \to W(k)$ a ring homomorphism, with $\bar\iota$ its reduction modulo $pW(k)$. Let $\Phi$ be a `FormalODModule` over $W(k)/pW(k)$, that is, a two-dimensional commutative formal group law with an action of $W(\mathbb F_{p^2})$ and an endomorphism $\varpi$ with $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$; assume $\Phi$ is special for $\bar\iota$ (the eigen-submodules $\mathrm{lieZero}$ and $\mathrm{lieOne}$ of its Lie algebra are complementary and invertible), has height $4$ (the kernel of $[p]$ has degree $p^4$), and that the induced map $\mathrm{lieVarpi}$ vanishes on $\mathrm{lieZero}$. Let $M$ be a moduli package over $W(k)$ satisfying the Zariski-sheaf condition $\mathrm{IsZariskiSheaf}$, and $\eta$ a rule sending a rigidified $\Phi$-object $t$ over a ring $B$ with a map $\psi : W(k)\to B$ and $p$ nilpotent to a point of $M(B,\psi)$, subject to three conditions: over Noetherian $B$, two admissible objects have the same image under $\eta$ exactly when they are isomorphic; $\eta$ commutes with base change along ring maps compatible with the structure maps; and every point of $M(B,\psi)$ becomes, after localising at each member of a finite family generating the unit ideal of $B$, the $\eta$-image of an admissible object. Let $h_{c\Phi}$ witness that the graded pieces of degrees $0$ and $1$ of the Cartier module of $\Phi$ are complementary, and let $r_\Phi : \mathbb Z_p^2 \to N$ be an additive map into the associated $N$-module which, for every canonical $L$-map, maps the whole of $\mathbb Z_p^2$ bijectively onto the degree-$0$ $\eta$-piece $\mathrm{etaPiece}$. Finally, let $\theta$ assign to each point of $M(B,\psi)$, for $B$ a Noetherian $\mathbb Z_p$-algebra, a Deligne datum over $B$ for $(\mathbb Q_p,\mathbb Z_p,p)$, and assume $\theta$ is a period map in the sense of `IsPeriodMap`: every Drinfeld datum forming a Cartier quadruple with an admissible $t$ is a quadruple of $\theta(\eta(t))$, and $\theta$ commutes with base change. The conclusion is the following local lifting property. Let $B,B'$ be Noetherian commutative $\mathbb Z_p$-algebras with maps $\psi : W(k)\to B$, $\psi' : W(k)\to B'$ and $p$ nilpotent in both, let $\varphi : B' \to B$ be a surjective $\mathbb Z_p$-algebra map with $\varphi\circ\psi'=\psi$ and $(\ker\varphi)\cdot(\ker\varphi)=\bot$, let $x \in M(B,\psi)$, and let $d'$ be a Deligne datum over $B'$ such that $\theta(x)$ is the base change of $d'$ along $\varphi$ (for every full lattice $N$, the line of $\theta(x)$ at $N$ is the $B$-span of the image of the line of $d'$ at $N$). Then there are finitely many elements $f_1,\dots,f_n$ of $B'$ generating the unit ideal such that for every index $i$, every Noetherian localisation $L'$ of $B'$ away from $f_i$, every Noetherian localisation $L$ of $B$ away from $\varphi(f_i)$, both with $p$ nilpotent, and every ring map $\varphi_L : L' \to L$ compatible with $\varphi$ and with the structure maps from $W(k)$, the fibre of $M(\varphi_L)$ over the image of $x$ in $M(L)$ is non-empty.
--
--   This is the non-emptiness half of the lifting property of Drinfeld's functor along a square-zero thickening, given a lift of the period point, as in Boutot–Carayol II (10.4); it asserts Zariski-local liftability only and prescribes nothing about the period of the lift. It is used in the proof that the period morphism is bijective on Noetherian test rings in the critical-index situation (`bijective_of_isNoetherianRing_of_lieVarpi_eq_zero`).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_IsPeriodMap_exists_cover_exists_map_eq_map_of_isBaseChange_of_ker_mul_ker_eq_bot_of_lieVarpi_eq_zero.lean

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
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.IsPeriodMap.exists_cover_exists_map_eq_map_of_isBaseChange_of_ker_mul_ker_eq_bot_of_lieVarpi_eq_zero
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
    (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B']
    [Algebra ℤ_[p] B] [Algebra ℤ_[p] B']
    (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
    (φ : B' →ₐ[ℤ_[p]] B) (hφ : (φ : B' →+* B).comp ψ' = ψ) (_hφs : Function.Surjective φ)
    (_hφ2 : RingHom.ker (φ : B' →+* B) * RingHom.ker (φ : B' →+* B) = ⊥)
    (x : M.obj B ψ hB) (d' : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B'),
    DeligneDatum.IsBaseChange (K := ℚ_[p]) (π := (p : ℤ_[p])) φ d' (θ B ψ hB x) →
    ∃ (n : ℕ) (f : Fin n → B'), Ideal.span (Set.range f) = ⊤ ∧
      ∀ (i : Fin n) (L' : Type) [CommRing L'] [IsNoetherianRing L'] [Algebra B' L'] [IsLocalization.Away (f i) L']
        (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (φ (f i)) L]
        (hL' : IsNilpotent (p : L')) (hL : IsNilpotent (p : L))
        (φL : L' →+* L) (_hφL : φL.comp (algebraMap B' L') = (algebraMap B L).comp (φ : B' →+* B))
        (hφLψ : φL.comp ((algebraMap B' L').comp ψ') = (algebraMap B L).comp ψ),
        (M.fibre hL' hL φL hφLψ (M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl x)).Nonempty) := by sorry
