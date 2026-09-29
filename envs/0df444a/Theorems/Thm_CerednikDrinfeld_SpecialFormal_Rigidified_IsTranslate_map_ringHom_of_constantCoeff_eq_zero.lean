-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsTranslate_map_ringHom_of_constantCoeff_eq_zero
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsTranslate.map_ringHom_of_constantCoeff_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/43cbddbb-e3be-5a7d-9697-9ff2cfc40b62
-- title:
--   Base change of translates of rigidified special formal modules
-- statement:
--   Let $p$ be a prime, let $O$ be a commutative ring and let $\Phi$ be a formal $\mathcal{O}_D$-module over $O/pO$ in the sense of `FormalODModule p (O ⧸ pIdeal p O)`. Fix a pair of power series $e \in$ `Series (O ⧸ pIdeal p O)`, i.e. a pair $(e_0,e_1)$ of elements of $(O/pO)[[X_0,X_1]]$, and natural numbers $k, m'$. Let $B$ and $B'$ be commutative rings, $\psi : O \to B$ and $g : B \to B'$ ring homomorphisms, and let $t, t'$ be rigidified objects over $B$: each consists of a formal $\mathcal{O}_D$-module $X$ over $B$, a natural number $n$, and a pair $\rho$ of power series over $B/pB$. Assume that all of the pairs $t.\rho$, $t'.\rho$ and $e$ have vanishing constant terms in both coordinates, and that `Rigidified.IsTranslate e k m' ψ t t'` holds, i.e. $t'.X = t.X$ and there is a $c \in \mathbb{N}$ with $$[p^{c+t.n+k}]_{\bar t.X} \circ \bigl(t'.\rho \circ \mathrm{Frob}^{m'}\bigr) = [p^{c+t'.n}]_{\bar t.X} \circ \bigl(t.\rho \circ (e_\psi \circ \mathrm{Frob}^{2k})\bigr),$$ where $\bar t.X$ is the reduction of $t.X$ modulo $p$, $[a]$ denotes the action series `act` of $a \in \mathbb{Z}_{p^2}$, $\mathrm{Frob}^{j}$ is the substitution $X_i \mapsto X_i^{p^{j}}$, $e_\psi$ is $e$ pushed forward along the induced map $O/pO \to B/pB$, and $\circ$ is substitution of pairs of power series. The conclusion is that the base changes $t.\mathrm{map}\,g$ and $t'.\mathrm{map}\,g$ (apply $g$ coefficientwise to $X$, keep $n$, and push $\rho$ along the induced map $B/pB \to B'/pB'$) again satisfy `Rigidified.IsTranslate e k m' (g ∘ ψ) _ _`, with the same $k$, $m'$ and $e$.
--
--   This is the base-change compatibility of the translation relation between rigidified special formal modules of height $4$ along a ring homomorphism of the base, one of the functoriality statements underlying the Čerednik–Drinfeld description of the formal upper half plane. It is used in the study of fake elliptic curves, in the constructions producing a scalar $p$-power action identifying Frobenius twists of points of the functor $G$ with translates realised by the relative Frobenius and the Verschiebung.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsTranslate_map_ringHom_of_constantCoeff_eq_zero.lean

import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsTranslate.map_ringHom_of_constantCoeff_eq_zero
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (e : Series (O ⧸ pIdeal p O)) (k m' : ℕ)
    {B B' : Type} [CommRing B] [CommRing B'] (ψ : O →+* B) (g : B →+* B')
    (t t' : Rigidified p Φ B)
    (hρ : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0) (hρ' : ∀ i, MvPowerSeries.constantCoeff (t'.ρ i) = 0)
    (he : ∀ i, MvPowerSeries.constantCoeff (e i) = 0)
    (h : Rigidified.IsTranslate e k m' ψ t t') :
    Rigidified.IsTranslate e k m' (g.comp ψ) (t.map g) (t'.map g) := by sorry
