-- Prove2me | Theorems.Thm_FermiGaussMix_lemma_B_6
-- name    : FermiGaussMix.lemma_B_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:00:27.660107+00:00
-- url     : https://prove2.me/theorems/065472d1-023c-4816-9f9b-2ccd8f320bdc
-- title:
--   Lemma B.6 — $L_q([A,Y])\le\frac{2k}{q^2}J_q(A)L_q(Y)$
-- statement:
--   Let $q\ge 1$. Suppose that $A$ and $Y$ are even and that every Majorana monomial in $Y$ has degree at most $k$. Then
--   $$
--   L_q([A,Y])\le\frac{2k}{q^2}J_q(A)L_q(Y).
--   $$
--   This controls the coefficient growth of nested commutators.
--
--   Differences from the source:
--   - encoding: Majorana operators γ_a satisfying (A.1) → the published Jordan–Wigner operators FermiCap.Gaussian.majorana, labels Fin (2 * n), 0-based; reason: any family with (A.1) on a 2^n-dimensional space is unitarily equivalent to this one, and all objects here are unitarily covariant
-- source:
--   Han, Zhao, Liu, Weakly interacting fermionic Gibbs states are Gaussian mixtures and classically simulable, arXiv:2609.35159v1, Lemma B.6, p. 20

import Mathlib
import Definitions.Def_FermiGaussMix_coeff

open scoped BigOperators
open Matrix FermiCap.Gaussian

namespace FermiGaussMix

/-- **Lemma B.6, p.20** (Han, Zhao, Liu, arXiv:2609.35159v1). Let `q ≥ 1`. If `A` and `Y` are even and every Majorana
monomial in `Y` has degree at most `k`, then `L_q([A, Y]) ≤ (2k/q²) J_q(A) L_q(Y)`. -/
theorem lemma_B_6 {n k : ℕ} {q : ℝ} {A Y : Op n} (hq : 1 ≤ q) (hA : IsEvenOp A) (hY : IsEvenOp Y)
    (hk : HasDegreeLE k Y) :
    Lq q (A * Y - Y * A) ≤ (2 * (k : ℝ) / q ^ 2) * Jq q A * Lq q Y := by sorry

end FermiGaussMix
