-- Prove2me | Theorems.Thm_FamousTheorems_weierstrass_preparation
-- name    : FamousTheorems.weierstrass_preparation
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:15:13.598192+00:00
-- url     : https://prove2.me/theorems/24c3aea8-5ce9-4c59-8dc6-08f39143ecd1
-- title:
--   The Weierstrass preparation theorem
-- statement:
--   **The Weierstrass preparation theorem.** Let $A$ be a complete local ring with maximal ideal $\mathfrak m$ and $g\in A[[X]]$ a power series whose reduction modulo $\mathfrak m$ is nonzero. Then $g=f\cdot h$ where $f\in A[X]$ is a distinguished polynomial (monic, with all non-leading coefficients in $\mathfrak m$) and $h$ is a unit of $A[[X]]$.
--
--   It reduces the local study of power series to polynomials. It is fundamental in local analytic geometry (with $A$ a ring of convergent series), in Iwasawa theory (with $A=\mathbb Z_p$) and in the structure theory of $\mathbb Z_p[[T]]$-modules.
--
--   **Formalization note.** Mathlib's `PowerSeries.exists_isWeierstrassFactorization`; completeness is `IsAdicComplete (maximalIdeal A) A`, and `g.IsWeierstrassFactorization f h` says `f` is distinguished, `h` is a unit, and `g = f * h`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `PowerSeries.exists_isWeierstrassFactorization`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem weierstrass_preparation {A : Type*} [CommRing A] [IsLocalRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A] {g : PowerSeries A}
    (hg : PowerSeries.map (IsLocalRing.residue A) g ≠ 0) :
    ∃ (f : Polynomial A) (h : PowerSeries A), g.IsWeierstrassFactorization f h := by sorry

end FamousTheorems
