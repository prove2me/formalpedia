-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_isODHom_frobSeries_map_of_forall_eq_pow
-- name    : CerednikDrinfeld.FormalODModule.isODHom_frobSeries_map_of_forall_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/7e42c00e-6ba6-54b3-9bd7-4595dd75282d
-- title:
--   Frobenius as a homomorphism between Frobenius-twisted base changes
-- statement:
--   Let $p$ be a prime, let $C$ and $D$ be commutative rings, let $f, g : C \to D$ be ring homomorphisms, and let $j$ be a natural number; assume $p = 0$ in $D$ and that $g(x) = f(x)^{p^{j}}$ for every $x \in C$. Let $G$ be a `FormalODModule p C`, that is: a $2$-dimensional formal group law $F$ over $C$ together with a commutativity witness, a family of pairs of power series $\mathrm{act}(a)$ indexed by $a \in \mathbb{Z}_{p^{2}}$ and a pair $\varpi$, each of which is an endomorphism of the law $F$, subject to $\mathrm{act}(1) = \mathrm{id}$, $\mathrm{act}(ab) = \mathrm{act}(a)\circ\mathrm{act}(b)$, $\mathrm{act}(a+b) = F(\mathrm{act}(a),\mathrm{act}(b))$, $\varpi\circ\varpi = \mathrm{act}(p)$ and $\varpi\circ\mathrm{act}(a) = \mathrm{act}(\varphi(a))\circ\varpi$ for the Witt-vector Frobenius $\varphi$. The assertion is that the pair of power series $(X_{0}^{p^{j}}, X_{1}^{p^{j}})$ over $D$, namely `Rigidified.frobSeries D j`, satisfies `IsODHom` from the coefficientwise pushforward $G\otimes_{f}D$ to the pushforward $G\otimes_{g}D$: its constant coefficients vanish, it transforms the group law of $G\otimes_{f}D$ into that of $G\otimes_{g}D$ in the two-variable sense of `IsLawHom`, and it commutes with every $\mathrm{act}(a)$ and with $\varpi$ of the two base changes.
--
--   This is the relative $j$-fold Frobenius isogeny $G\otimes_{C,f}D \to G\otimes_{C,g}D$ of special formal $\mathcal{O}_D$-modules in characteristic $p$, in the form used in the Čerednik–Drinfeld uniformisation. It is invoked in the rigidification theory for fake elliptic curves, for instance in the statements producing isogenies of prescribed height and admissible rigid transports.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_isODHom_frobSeries_map_of_forall_eq_pow.lean

import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.isODHom_frobSeries_map_of_forall_eq_pow
    {p : ℕ} [Fact p.Prime] {C : Type} [CommRing C] {D : Type} [CommRing D]
    (f g : C →+* D) (j : ℕ) (hp : (p : D) = 0) (hg : ∀ x : C, g x = (f x) ^ (p ^ j))
    (G : FormalODModule p C) :
    FormalODModule.IsODHom (G.map f) (G.map g) (Rigidified.frobSeries (p := p) D j) := by sorry
