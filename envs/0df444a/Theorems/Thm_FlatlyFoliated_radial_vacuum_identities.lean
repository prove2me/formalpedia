-- Prove2me | Theorems.Thm_FlatlyFoliated_radial_vacuum_identities
-- name    : FlatlyFoliated.radial_vacuum_identities
-- status  : Proved
-- author  : @fizzyinc3
-- created : 2026-10-17T17:25:32.922692+00:00
-- url     : https://prove2.me/theorems/4d874523-7e17-4180-8786-2df274da9911
-- title:
--   Exterior radial identities for the FFR vacuum equations
-- statement:
--   Let $\Lambda\in\mathbb R$, and let $(\omega,\eta)$ be a smooth vacuum solution of the Flatly Foliated Relativity equations (34)–(35) on $\mathbb R^3$, with $\eta>0$, spherically symmetric outside a ball. For the radial profiles along the positive first coordinate axis, write $a(r)=\omega_1(r,0,0)$ and $e(r)=\eta(r,0,0)$. There exists $R>0$ such that, for every $r>R$,
--
--   $$
--   \frac{d}{dr}\bigl(r a(r)^2\bigr)=\Lambda r^2e(r)^2,
--   \qquad a(r)e'(r)=0.
--   $$
--
--   These identities give the exterior ordinary differential equations for every sign of the cosmological constant. They separate the geometric reduction from the one-dimensional analysis used in the nonexistence and classification of spherical vacuum solutions.
-- source:
--   Bray–Hamm–Hirsch–Wheeler–Zhang, Flatly Foliated Relativity, arXiv:1911.00967v2, Section 5, proof of Lemma 3, equations (109)–(113); the radial calculation also appears in equations (96)–(99). https://arxiv.org/html/1911.00967v2

import Definitions.Def_FlatlyFoliatedRelativity_basic

open scoped ContDiff
open FlatlyFoliated

theorem FlatlyFoliated.radial_vacuum_identities (Λ : ℝ) (w : R3 → R3) (η : R3 → ℝ)
    (hw : ContDiff ℝ ∞ w) (hη : ContDiff ℝ ∞ η) (hηpos : ∀ x, 0 < η x)
    (heq : FFREquations Λ 0 0 w η) (hsph : SphSymmAtInfty w η) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R < r →
      HasDerivAt (fun s : ℝ => s * (w (EuclideanSpace.single 0 s) 0) ^ 2)
        (Λ * r ^ 2 * (η (EuclideanSpace.single 0 r)) ^ 2) r ∧
      w (EuclideanSpace.single 0 r) 0 *
        deriv (fun s : ℝ => η (EuclideanSpace.single 0 s)) r = 0 := by sorry
