-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Series_eq_of_comp_frobSeries_eq
-- name    : CerednikDrinfeld.SpecialFormal.Series.eq_of_comp_frobSeries_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/11a705fc-81b7-5e1b-a944-2a13ff5b31ae
-- title:
--   Precomposition with Xᵢ ↦ Xᵢ^{p^j} is injective
-- statement:
--   Let $p$ be a prime, let $B$ be a commutative ring, and let $j$ be a natural number. Here a `Series B` is a pair of formal power series in two variables over $B$, i.e. an element of `Fin 2 → MvPowerSeries (Fin 2) B`, and for two such pairs the composite `φ.comp χ` is the pair whose $i$-th component is the substitution of the components of $\chi$ into $\varphi_i$. The pair `Rigidified.frobSeries B j` is $(X_0^{p^j}, X_1^{p^j})$, that is, its $i$-th component is $X_i^{p^j}$. The assertion is: if $\varphi, \psi$ are pairs of power series in two variables over $B$ such that substituting $X_i \mapsto X_i^{p^j}$ into each component of $\varphi$ gives the same pair as substituting $X_i \mapsto X_i^{p^j}$ into each component of $\psi$, then $\varphi = \psi$. No hypothesis on the characteristic of $B$ is needed, and the case $j = 0$, where the substituted pair is the identity pair, is included.
--
--   This is the elementary cancellation statement that a $j$-fold Frobenius-type substitution on the variables may be removed from the right of a composition of power series pairs. It is used when comparing transports of a rigidification with those of its Frobenius re-basing, in the lemmas [`CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_represents_comp_act_pow_eq_of_isRigTransport_of_act_comp_hom_comp_eq`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_represents_comp_act_pow_eq_of_isRigTransport_of_act_comp_hom_comp_eq) and [`CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isTranslate_id_zero_zero_of_isRigTransport_zero_of_comp_frobSeries_eq_act_comp`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isTranslate_id_zero_zero_of_isRigTransport_zero_of_comp_frobSeries_eq_act_comp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Series_eq_of_comp_frobSeries_eq.lean

import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Series.eq_of_comp_frobSeries_eq
    {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] (j : ℕ) (φ ψ : Series B)
    (h : φ.comp (Rigidified.frobSeries (p := p) B j) = ψ.comp (Rigidified.frobSeries (p := p) B j)) :
    φ = ψ := by sorry
