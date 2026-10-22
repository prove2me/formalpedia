-- Prove2me | Theorems.Thm_BraneBrauer_Orthogonal_eq_7_8
-- name    : BraneBrauer.Orthogonal.eq_7_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:30.971514+00:00
-- url     : https://prove2.me/theorems/67d71850-b5ef-4354-9f7a-5276dddbb74a
-- title:
--   (7.8) — Gaussian oscillator covariance
-- statement:
--   For the two independent $N\times N$ Gaussian matrices $Z_A,Z_B$ and any indices $i,j,k,l$, the same-matrix covariance is
--   $$
--   \mathbb E[\overline{(Z_A)_{ji}}(Z_A)_{kl}]
--   =\mathbb E[\overline{(Z_B)_{ji}}(Z_B)_{kl}]
--   =\delta_{il}\delta_{kj},
--   $$
--   while both mixed covariances between $Z_A$ and $Z_B$ vanish.
--
--   This is the vacuum two-point normalization behind the oscillator relations (7.8) and fixes the index orientation used by the Wick expansion.
--
--   **Formalization Note** The claim is for the Gaussian realization of the vacuum expectation, rather than an abstract commutator algebra; $N$ may be zero, in which case there are no indices to instantiate.
-- source:
--   Kimura & Ramgoolam, Branes, Anti-Branes and Brauer Algebras in Gauge-Gravity duality, arXiv:0709.2158v2, p. 28, (7.8)

import Mathlib
import Definitions.Def_BraneBrauer_Orthogonal_Setting

noncomputable section

namespace BraneBrauer.Orthogonal

/-- (7.8), p. 28: the two independent oscillator matrices have unit
cross-index covariance and zero mixed covariance in the Gaussian model. -/
theorem eq_7_8 {N : ℕ} (i j k l : Fin N) :
    (∫ Z, star (Z 0 j i) * Z 0 k l ∂matrixGaussian N) =
        (if i = l ∧ k = j then (1 : ℂ) else 0) ∧
    (∫ Z, star (Z 1 j i) * Z 1 k l ∂matrixGaussian N) =
        (if i = l ∧ k = j then (1 : ℂ) else 0) ∧
    (∫ Z, star (Z 0 j i) * Z 1 k l ∂matrixGaussian N) = 0 ∧
    (∫ Z, star (Z 1 j i) * Z 0 k l ∂matrixGaussian N) = 0 := by sorry

end BraneBrauer.Orthogonal
