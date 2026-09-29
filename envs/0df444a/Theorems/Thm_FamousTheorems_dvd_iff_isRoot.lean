-- Prove2me | Theorems.Thm_FamousTheorems_dvd_iff_isRoot
-- name    : FamousTheorems.dvd_iff_isRoot
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T22:10:32.207832+00:00
-- url     : https://prove2.me/theorems/a47d0812-4a92-4078-9704-724e43a4b4e2
-- title:
--   The factor theorem
-- statement:
--   **$(X - a)$ divides $p$ if and only if $a$ is a root.**
--
--   $$(X-a) \mid p \iff p(a) = 0 .$$
--
--   Dividing $p$ by $X - a$ with remainder gives $p = (X-a)q + r$ with $r$ constant; evaluating at
--   $a$ shows $r = p(a)$. So the remainder theorem and the factor theorem are the same statement,
--   and the division algorithm works over any commutative ring because $X - a$ is monic.
--
--   The immediate consequence is that a non-zero polynomial of degree $n$ over an integral domain
--   has at most $n$ roots — which is what makes polynomial interpolation unique, underlies
--   Lagrange interpolation and Reed–Solomon codes, and fails over non-domains such as
--   $\mathbb{Z}/8$, where $x^2-1$ has four roots.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

theorem dvd_iff_isRoot : ∀ {R : Type*} {a : R} [CommRing R] {p : Polynomial R},
    (Polynomial.X - Polynomial.C a) ∣ p ↔ p.IsRoot a := by sorry

end FamousTheorems
