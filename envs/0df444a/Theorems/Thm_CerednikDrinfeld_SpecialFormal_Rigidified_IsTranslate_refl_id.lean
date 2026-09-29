-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsTranslate_refl_id
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsTranslate.refl_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/7d57f7e6-9dd3-5b45-8ec7-d176f5b1cb5b
-- title:
--   Reflexivity of the translate relation on rigidified modules
-- statement:
--   Let $p$ be a prime, $O$ a commutative ring and $\Phi$ a formal $\mathcal{O}_D$-module over $O/pO$ (an object of `FormalODModule p (O ⧸ pIdeal p O)`, i.e. a two-variable commutative formal group law together with series realising a $\mathbb{Z}_{p^2}$-action and a uniformiser series $\varpi$ with $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\sigma(a)]\circ\varpi$). Let $B$ be a commutative ring, $\psi : O \to B$ a ring homomorphism, and $t$ a rigidified module over $B$, that is a triple consisting of a formal $\mathcal{O}_D$-module $t.X$ over $B$, a natural number $t.n$, and a pair of power series $t.\rho$ in two variables over $B/pB$. The assertion is that `Rigidified.IsTranslate` holds for $t$ and $t$ with translation data $e =$ the identity series on $O/pO$, $k = 0$ and $m' = 0$ and with the homomorphism $\psi$: namely $t.X = t.X$, and there exists $c \in \mathbb{N}$ such that $[p^{\,c+t.n+0}]$ (the action on `t.Xbar`) composed after $t.\rho \circ \mathrm{Frob}^{0}$ equals $[p^{\,c+t.n}]$ composed after $t.\rho \circ \bigl((\text{reduction of the identity series along } \psi) \circ \mathrm{Frob}^{0}\bigr)$, where $\mathrm{Frob}^{j}$ denotes the series $(X_i \mapsto X_i^{p^j})$ and all compositions are substitution of series.
--
--   This is the reflexivity statement for the translate relation between rigidified special formal modules of the Čerednik–Drinfel'd uniformisation, taken with trivial translation data $(\mathrm{id},0,0)$; it is what produces the identity element of the group action on Drinfel'd's functor at the level of rigidifications. It is used in the construction of fake elliptic curves, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isActBy_scalar_zpow_rigidifiedToG_frobTwist_neg_one_of_comp_verschiebung`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isActBy_scalar_zpow_rigidifiedToG_frobTwist_neg_one_of_comp_verschiebung).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsTranslate_refl_id.lean

import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsTranslate.refl_id
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    {B : Type} [CommRing B] (ψ : O →+* B) (t : Rigidified p Φ B) :
    Rigidified.IsTranslate (Series.id (O ⧸ pIdeal p O)) 0 0 ψ t t := by sorry
