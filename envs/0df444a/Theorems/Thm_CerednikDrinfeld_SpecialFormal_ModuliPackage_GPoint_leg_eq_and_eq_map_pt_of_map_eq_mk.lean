-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_GPoint_leg_eq_and_eq_map_pt_of_map_eq_mk
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.leg_eq_and_eq_map_pt_of_map_eq_mk
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/110c76c9-aaa0-54f0-a0e8-adab4c22816a
-- title:
--   Componentwise reading of a pushed-forward G_Φ-point
-- statement:
--   Fix a prime $r$, a commutative ring $\mathcal O$, a commutative $\mathcal O$-algebra $Onr$, a formal $\mathcal O_D$-module $\Phi$ of height data $r$ over $Onr/(r)$, and a moduli package $M$ for $r$ over $Onr$, i.e. an assignment $B \mapsto M.\mathrm{obj}\,B\,\psi\,h$ for each commutative ring $B$, ring homomorphism $\psi : Onr \to B$ and proof that $r$ is nilpotent in $B$, together with functorial transport maps along ring homomorphisms compatible with the legs. Let $\eta$ be a family of maps $\mathrm{Rigidified}\,r\,\Phi\,B \to M.\mathrm{obj}\,B\,\psi\,h$, one for each such $(B,\psi,h)$, where a rigidified object over $B$ consists of a formal $\mathcal O_D$-module $X$ over $B$, a natural number $n$ and a series $\rho$ over $B/(r)$; no naturality is assumed of $\eta$. Let $B$ and $L$ be commutative $\mathcal O$-algebras, $\varphi : B \to L$ an $\mathcal O$-algebra map, and $x$ a $G$-point over $B$, that is a triple consisting of an $\mathcal O$-algebra map $x.\psi : Onr \to B$, a witness $x.\mathrm{nilp}$ that $r$ is nilpotent in $B$, and a point $x.\mathrm{pt}$ of $M.\mathrm{obj}\,B\,x.\psi\,x.\mathrm{nilp}$. Let $\chi : Onr \to L$ be an $\mathcal O$-algebra map, $hL$ a witness that $r$ is nilpotent in $L$, and $t$ a rigidified object over $L$. Assume the pushforward $x.\mathrm{map}\,\varphi$, whose components are $\varphi \circ x.\psi$ and the transport of $x.\mathrm{pt}$ along $\varphi$, equals the triple $(\chi, hL, \eta_L(\chi)(t))$. Then $\chi = \varphi \circ x.\psi$, and $\eta_L(\varphi \circ x.\psi)(t)$ equals the transport of $x.\mathrm{pt}$ along $\varphi$ in $M.\mathrm{obj}\,L\,(\varphi \circ x.\psi)\,hL$.
--
--   This is the componentwise reading of an equality of points of the functor $G_\Phi$ built from a moduli package: it separates the identification of the coefficient leg from the identification of the moduli point, the latter living a priori in a type indexed by the leg. It is used in the comparison of fake elliptic curves with rigidified formal modules, where an equality of $G_\Phi$-points produced by a naturality argument must be turned into an equation between a point coming from $\eta$ and a transported point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_GPoint_leg_eq_and_eq_map_pt_of_map_eq_mk.lean

import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.GPoint.leg_eq_and_eq_map_pt_of_map_eq_mk
    {r : ℕ} [Fact r.Prime] {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {Φ : FormalODModule r (Onr ⧸ pIdeal r Onr)} {M : ModuliPackage.{0, 0} r Onr}
    (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)), Rigidified r Φ B → M.obj B ψ hB)
    {B L : Type} [CommRing B] [Algebra 𝒪 B] [CommRing L] [Algebra 𝒪 L] (φ : B →ₐ[𝒪] L)
    (x : ModuliPackage.GPoint 𝒪 M B) (χ : Onr →ₐ[𝒪] L) (hL : IsNilpotent (r : L)) (t : Rigidified r Φ L)
    (h : x.map φ = ⟨χ, hL, η L (χ : Onr →+* L) hL t⟩) :
    χ = φ.comp x.ψ ∧
      η L ((φ : B →+* L).comp (x.ψ : Onr →+* B)) hL t =
        M.map (ψ' := (φ : B →+* L).comp (x.ψ : Onr →+* B)) x.nilp hL (φ : B →+* L) rfl x.pt := by sorry
