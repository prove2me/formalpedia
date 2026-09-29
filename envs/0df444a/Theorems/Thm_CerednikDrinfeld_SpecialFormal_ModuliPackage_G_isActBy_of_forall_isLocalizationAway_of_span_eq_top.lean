-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_G_isActBy_of_forall_isLocalizationAway_of_span_eq_top
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.G.isActBy_of_forall_isLocalizationAway_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/324f7f46-2944-5eaa-b344-c6edd320818d
-- title:
--   Zariski-local criterion for GL₂-action on Drinfeld's functor
-- statement:
--   Fix a prime $r$, a commutative ring $\mathcal O$, a commutative $\mathcal O$-algebra $Onr$ with an $\mathcal O$-algebra automorphism $Fr$, a ring homomorphism $\iota$ from the Witt vectors of $\mathbb F_{r^2}$ to $Onr$, a formal $\mathcal O_D$-module $\Phi$ of dimension $2$ over $Onr/(r)$, a moduli package $M$ over $Onr$ (a functor assigning to each ring $B$ with a map $\psi : Onr \to B$ and $r$ nilpotent in $B$ a type, with functorial base change), and a family $\eta$ sending rigidified objects over $B$ to points of $M$. Let $K_0$ be a field that is an $\mathcal O$-algebra and $E_0$ a ring homomorphism from the centraliser of $\{\Phi.\mathrm{actEnd}\,a\} \cup \{\Phi.\mathrm{varpiEnd}\}$ in $\mathrm{End}(\Phi.F)$ to $M_2(K_0)$, and let $x,x'$ be points of $M$ over an $\mathcal O$-algebra $B$, each consisting of an $\mathcal O$-algebra map $Onr \to B$, nilpotence of $r$ in $B$, and a point of $M$. Given $e$ in that centraliser, naturals $k,m'$ and $g \in \mathrm{GL}_2(K_0)$ with $E_0 e = r^k \cdot g^{-1}$ and with the power-series family of $e$ having kernel of degree $r^{2m'}$ (its kernel algebra finite projective over the base of constant rank $r^{2m'}$ after any map to a field), and given $f_1,\dots,f_n \in B$ generating the unit ideal such that, for each $i$ and each $B$-algebra $L$ realising the localisation of $B$ away from $f_i$, (i) the coefficient legs of $x'$ and of the $Fr^{\,m'-2k}$-twist of the leg of $x$ agree after $B \to L$, and (ii) whenever $r$ is nilpotent in $L$ there are rigidified objects $t,t'$ over $L$, admissible for $\iota$ and the respective composed legs, whose $\eta$-images are the base changes of the points of $x$ and $x'$ and with $t'$ an $(e,k,m')$-translate of $t$ over the composed leg of $x$, the conclusion is that $x'$ is obtained from $x$ by the action of $g$ in the sense of `ModuliPackage.G.IsActBy`, that is, there exist $e,k,m'$ satisfying the two conditions above together with the global leg identity $x'.\psi = Fr^{\,m'-2k}$-twist of $x.\psi$ and the local-lifting condition over a basic open cover.
--
--   This is the statement that the $\mathrm{GL}_2(K_0)$-action relation on Drinfeld's functor is Zariski-local on the base: local translate data over a cover by basic opens of $\operatorname{Spec} B$ suffices to exhibit $x'$ as the $g$-translate of $x$. It is used in the construction of the action on the fake-elliptic-curve side, in the assembly of the equivalence between rigidified formal modules and the moduli functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_G_isActBy_of_forall_isLocalizationAway_of_span_eq_top.lean

import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.G.isActBy_of_forall_isLocalizationAway_of_span_eq_top
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    (Fr : Onr ≃ₐ[𝒪] Onr) (ι : Zp2 r →+* Onr) (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
    (M : ModuliPackage.{0, 0} r Onr)
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)), Rigidified r Φ B → M.obj B ψ hB)
    {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀]
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (x x' : ModuliPackage.GPoint 𝒪 M B)

    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (k m' : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) K₀)
    (hE : E₀ e = (r : K₀) ^ k • ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))
    (hker : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')))

    (n : ℕ) (f : Fin n → B) (hspan : Ideal.span (Set.range f) = ⊤)

    (hleg : ∀ (i : Fin n) (L : Type) [CommRing L] [Algebra B L] [IsLocalization.Away (f i) L],
      (algebraMap B L).comp (x'.ψ : Onr →+* B) = (algebraMap B L).comp ((frobTwist Onr Fr ((m' : ℤ) - 2 * k) x.ψ : Onr →ₐ[𝒪] B) : Onr →+* B))

    (hloc : ∀ (i : Fin n) (L : Type) [CommRing L] [Algebra B L] [IsLocalization.Away (f i) L]
      (hL : IsNilpotent (r : L)),
      ∃ t t' : Rigidified r Φ L,
        t.IsAdmissible ι ((algebraMap B L).comp (x.ψ : Onr →+* B)) ∧ t'.IsAdmissible ι ((algebraMap B L).comp (x'.ψ : Onr →+* B)) ∧
        η L ((algebraMap B L).comp (x.ψ : Onr →+* B)) hL t =
          M.map (ψ' := (algebraMap B L).comp (x.ψ : Onr →+* B)) x.nilp hL (algebraMap B L) rfl x.pt ∧
        η L ((algebraMap B L).comp (x'.ψ : Onr →+* B)) hL t' =
          M.map (ψ' := (algebraMap B L).comp (x'.ψ : Onr →+* B)) x'.nilp hL (algebraMap B L) rfl x'.pt ∧
        Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries k m' ((algebraMap B L).comp (x.ψ : Onr →+* B)) t t') :
    ModuliPackage.G.IsActBy ι Φ η Fr E₀ g x x' := by sorry
