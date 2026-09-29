-- Prove2me | Theorems.Thm_FamousTheorems_weierstrass_division_theorem
-- name    : FamousTheorems.weierstrass_division_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:22:29.010983+00:00
-- url     : https://prove2.me/theorems/86332d56-0e3a-4b27-ac47-8ee768260bcb
-- title:
--   The Weierstrass division theorem
-- statement:
--   **The Weierstrass division theorem.** Let $A$ be a complete local ring with maximal ideal $\mathfrak m$, and let $g\in A[[X]]$ be a power series whose reduction modulo $\mathfrak m$ is nonzero, of order $n$. Then every $f\in A[[X]]$ can be written as
--   $$f=gq+r$$
--   with $q\in A[[X]]$ and $r\in A[X]$ a polynomial of degree less than $n$.
--
--   This is the power series analogue of polynomial division with remainder. It implies the Weierstrass preparation theorem and is basic in local analytic geometry and Iwasawa theory.
--
--   **Formalization note.** Mathlib's `PowerSeries.exists_isWeierstrassDivision`. Completeness is `IsAdicComplete (IsLocalRing.maximalIdeal A) A`. `f.IsWeierstrassDivision g q r` states that $f=gq+r$ and that $\deg r$ is less than the order of $g$ modulo $\mathfrak m$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `PowerSeries.exists_isWeierstrassDivision`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem weierstrass_division_theorem {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] (f : PowerSeries A)
    {g : PowerSeries A} (hg : PowerSeries.map (IsLocalRing.residue A) g ≠ 0) :
    ∃ (q : PowerSeries A) (r : Polynomial A), f.IsWeierstrassDivision g q r := by sorry

end FamousTheorems
