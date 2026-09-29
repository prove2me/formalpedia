-- Prove2me | Theorems.Thm_AddSubgroup_galois_trivial_quotient_of_inertia_absorbing
-- name    : AddSubgroup.galois_trivial_quotient_of_inertia_absorbing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.565368+00:00
-- url     : https://prove2.me/theorems/2b520074-31e0-55b5-b05d-fdb54a2aab06
-- title:
--   Global triviality of p^m-torsion displacements from inertia
-- statement:
--   Let $W$ be a Weierstrass curve over $\mathbb{Z}$, let $p$ be a prime and $m$ a natural number with $1\le m$, and write $E$ for the base change of $W$ along $\mathbb{Z}\to\mathbb{Q}$, viewed over $\bar{\mathbb{Q}}=$ `AlgebraicClosure ℚ`, so that $E(\bar{\mathbb{Q}})$ is the group of affine Weierstrass points of that base change. Let $K$ be an additive subgroup of $E(\bar{\mathbb{Q}})$; no Galois stability of $K$ is assumed. Two hypotheses are made. First, the set of $\sigma\in\mathrm{Aut}_{\mathbb{Q}}(\bar{\mathbb{Q}})$ acting as the identity on the $\mathbb{Z}$-torsion submodule $\{x : p^m x = 0\}$ of $E(\bar{\mathbb{Q}})$ is open in the Krull topology. Second, for every prime $\ell$, every valuation subring $A$ of $\bar{\mathbb{Q}}$ whose nonunits contain the image of $\ell$, and every $\tau$ in the image in $\mathrm{Aut}_{\mathbb{Q}}(\bar{\mathbb{Q}})$ of the inertia subgroup of $A$ under the inclusion of the decomposition subgroup, one has $\tau y - y \in K$ for all $y\in E(\bar{\mathbb{Q}})$ with $p^m y = 0$. The conclusion is that $\sigma y - y \in K$ for every $\sigma\in\mathrm{Aut}_{\mathbb{Q}}(\bar{\mathbb{Q}})$ and every $y$ with $p^m y = 0$.
--
--   This is the passage from local (inertial) to global triviality of the Galois displacements on $E[p^m]$ modulo $K$, resting on the absence of nontrivial everywhere-unramified extensions of $\mathbb{Q}$; in the shape used here it is one step of the finite-level form of Mazur's reductions. It is cited in the analysis of Frey packages, in [`FreyPackage.frey_no_cofixed_large`](thm.html#FreyPackage.frey_no_cofixed_large).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AddSubgroup_galois_trivial_quotient_of_inertia_absorbing.lean

import Mathlib
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_ZeroComponentAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point ValuationSubring

theorem AddSubgroup.galois_trivial_quotient_of_inertia_absorbing
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : 1 ≤ m)
    (K : AddSubgroup ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hopen : IsOpen {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ |
      ∀ x : Submodule.torsionBy ℤ
        ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point ((p ^ m : ℕ) : ℤ),
      σ • x = x})
    (hInert : ∀ ℓ : ℕ, ℓ.Prime →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∀ τ ∈ A.inertiaSubgroupIn ℚ,
      ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      p ^ m • y = 0 → τ • y - y ∈ K) :
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ∀ y : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point,
      p ^ m • y = 0 → σ • y - y ∈ K := by sorry
