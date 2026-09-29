-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_nthSeries_pow_comp_comp_act_inv_eq_of_nthSeries_mul_comp_eq
-- name    : CerednikDrinfeld.FormalODModule.nthSeries_pow_comp_comp_act_inv_eq_of_nthSeries_mul_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/15b59fa3-8454-5965-a823-6aff9369eb0a
-- title:
--   Cancelling unit factors in an identity of mathcal O_D-module series
-- statement:
--   Fix a prime $p$ and commutative rings $B$, $R_0$, $S$. Let $X$ be a formal $\mathcal O_D$-module over $B$ and $X_0$ one over $R_0$ (in each case: a commutative two-dimensional formal group law together with an action of $\mathrm{Zp2}\,p=W(\mathbb F_{p^2})$ by endomorphism series and a uniformiser series satisfying the usual relations), and let $f : B \to S$, $g : R_0 \to S$ be ring homomorphisms. Let $\sigma$, $\sigma_f$, $\varepsilon$ be triples of pairs of power series in two variables over $S$, each component having vanishing constant term. Assume that $\sigma_f$ intertwines multiplication by every natural number: for all $m$, $[m]_X \circ \sigma_f = \sigma_f \circ [m]_{X_0}$, where $[m]$ denotes `nthSeries` of the relevant formal group law (the $m$-fold multiplication series, defined recursively by $[0]=0$, $[m+1]=F([m],X)$), pushed to $S$ along $f$ respectively $g$. Let $u$, $v$, $\alpha$, $\beta$ be naturals with the images of $u$ and $v$ in $W(\mathbb F_{p^2})$ units, and suppose $[u p^{\alpha}]_X \circ (\sigma \circ \varepsilon) = [u v p^{\beta}]_X \circ \sigma_f$, all composition being substitution of the right-hand pair into the left. Then $[p^{\alpha}]_X \circ \bigl(\sigma \circ (\varepsilon \circ \langle v^{-1}\rangle_{X_0})\bigr) = [p^{\beta}]_X \circ \sigma_f$, where $\langle v^{-1}\rangle_{X_0}$ is the action of the inverse of the unit $v$ on $X_0$, read in $S$ through $g$.
--
--   A bookkeeping step in the Čerednik–Drinfel'd dictionary for supersingular points: it removes the prime-to-$p$ unit factors $u$ and $v$ from an identity between representing series, leaving only the powers of $p$ that record the $p$-adic part of a degree. It is used in the rigidification lemmas [`CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isTranslate_of_isRigTransport_mapPt_of_comp_act_eq_comp_act_of_germ_of_isUnit`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.isTranslate_of_isRigTransport_mapPt_of_comp_act_eq_comp_act_of_germ_of_isUnit) and [`CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_add_eq_add_two_mul_and_add_add_eq_add_add_of_isRigTransport_mapPt_of_comp_act_eq_comp_act_of_germ_of_isUnit`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.exists_add_eq_add_two_mul_and_add_add_eq_add_add_of_isRigTransport_mapPt_of_comp_act_eq_comp_act_of_germ_of_isUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_nthSeries_pow_comp_comp_act_inv_eq_of_nthSeries_mul_comp_eq.lean

import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.nthSeries_pow_comp_comp_act_inv_eq_of_nthSeries_mul_comp_eq
    {p : ℕ} [Fact p.Prime] {B R₀ S : Type} [CommRing B] [CommRing R₀] [CommRing S]
    (X : FormalODModule p B) (X₀ : FormalODModule p R₀) (f : B →+* S) (g : R₀ →+* S)
    (σ σf ε : Series S)
    (hσ0 : ∀ i, MvPowerSeries.constantCoeff (σ i) = 0) (hσf0 : ∀ i, MvPowerSeries.constantCoeff (σf i) = 0)
    (hε0 : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0)
    (hlin : ∀ m : ℕ, (Series.map f (X.F.nthSeries m)).comp σf = σf.comp (Series.map g (X₀.F.nthSeries m)))
    (u v α β : ℕ) (hu : IsUnit ((u : ℕ) : Zp2 p)) (hv : IsUnit ((v : ℕ) : Zp2 p))
    (h : (Series.map f (X.F.nthSeries (u * p ^ α))).comp (σ.comp ε) =
      (Series.map f (X.F.nthSeries (u * v * p ^ β))).comp σf) :
    (Series.map f (X.F.nthSeries (p ^ α))).comp (σ.comp (ε.comp (Series.map g (X₀.act ((hv.unit⁻¹ : (Zp2 p)ˣ) : Zp2 p))))) =
      (Series.map f (X.F.nthSeries (p ^ β))).comp σf := by sorry
