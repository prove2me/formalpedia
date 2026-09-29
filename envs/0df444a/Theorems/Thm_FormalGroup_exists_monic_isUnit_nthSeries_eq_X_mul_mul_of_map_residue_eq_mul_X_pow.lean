-- Prove2me | Theorems.Thm_FormalGroup_exists_monic_isUnit_nthSeries_eq_X_mul_mul_of_map_residue_eq_mul_X_pow
-- name    : FormalGroup.exists_monic_isUnit_nthSeries_eq_X_mul_mul_of_map_residue_eq_mul_X_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/1e80d32f-d1e2-52f4-882a-0c8930ef5f2c
-- title:
--   Weierstrass preparation of the [q]-series in the height-one case
-- statement:
--   Let $S$ be a commutative Noetherian local ring that is adically complete with respect to its maximal ideal $\mathfrak m_S$, let $q$ be a prime number, and let $F$ be a one-dimensional formal group law over $S$. Write $F.\mathrm{nthSeries}\,q \in S[[X]]$ for the $q$-th iterate series, defined recursively by $\mathrm{nthSeries}\,0 = 0$ and $\mathrm{nthSeries}\,(n+1) = F(\mathrm{nthSeries}\,n, X)$, i.e. the multiplication-by-$q$ series of $F$. Assume that the reduction of this series along the residue map $S \to S/\mathfrak m_S$ is of the form $u \cdot X^{q}$ for some unit $u$ of the power series ring over the residue field. The conclusion asserts the existence of a polynomial $g \in S[X]$ and a power series $v \in S[[X]]$ such that: $g$ is monic; $g$ has degree $q-1$; every coefficient $g_i$ with $i < q-1$ lies in $\mathfrak m_S$; the constant coefficient of $g$ equals $q \cdot w$ for some unit $w \in S$; $v$ is a unit of $S[[X]]$; and $F.\mathrm{nthSeries}\,q = X \cdot g \cdot v$ in $S[[X]]$, $g$ being viewed in $S[[X]]$.
--
--   This is the Weierstrass (Lubin–Tate) factorisation of the multiplication-by-$q$ series of a formal group whose reduction has height one: $[q]_F = X\, g\, v$ with $g$ monic of degree $q-1$ and Eisenstein-type, its constant term being $q$ times a unit. It is the source of the Igusa-style presentation $S[X]/(g)$ of the $q$-torsion of the formal group, and is used in the two statements about level structures producing algebra isomorphisms of adjoined roots over power series rings in the moduli package for modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FormalGroup_exists_monic_isUnit_nthSeries_eq_X_mul_mul_of_map_residue_eq_mul_X_pow.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing Polynomial

theorem FormalGroup.exists_monic_isUnit_nthSeries_eq_X_mul_mul_of_map_residue_eq_mul_X_pow
    (S : Type*) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] [IsAdicComplete (maximalIdeal S) S]
    (q : ℕ) [Fact q.Prime] (F : FormalGroup S)
    (hF : ∃ u : PowerSeries (ResidueField S), IsUnit u ∧
      PowerSeries.map (residue S) (F.nthSeries q) = u * PowerSeries.X ^ q) :
    ∃ (g : S[X]) (v : PowerSeries S), g.Monic ∧ g.natDegree = q - 1 ∧
      (∀ i < q - 1, g.coeff i ∈ maximalIdeal S) ∧
      (∃ w : S, IsUnit w ∧ g.coeff 0 = (q : S) * w) ∧ IsUnit v ∧
      F.nthSeries q = PowerSeries.X * (↑g : PowerSeries S) * v := by sorry
