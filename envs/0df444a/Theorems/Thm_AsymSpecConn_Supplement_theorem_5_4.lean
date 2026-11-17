-- Prove2me | Theorems.Thm_AsymSpecConn_Supplement_theorem_5_4
-- name    : AsymSpecConn.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:29:02.813878+00:00
-- url     : https://prove2.me/theorems/0fca3185-a1df-4ae7-a4d7-c050fc7cf9db
-- title:
--   Theorem 5.4 — interpolation recovers the singleton upper quantum functional
-- statement:
--   For every probability vector $\theta\in\mathcal P([k])$, including boundary vectors with zero coordinates, the asymptotic interpolation of the weighted flattening-rank product $w_\theta=\prod_iR_i^{\theta_i}$ equals the singleton upper quantum functional $F^\theta$ pointwise. In particular,
--
--   $$
--   F^\theta\in\Delta.
--   $$
--
--   Thus the quantum functional is a monotone semiring homomorphism for tensor restriction.
--
--   Differences from the source:
--   - encoding: $F^\theta$ is defined by a base-two isotypic-support entropy supremum → $F^\theta$ is the exponential of the natural-entropy maximum over the equivalent entanglement polytope; reason: the moment-polytope and isotypic-support formulations are equivalent, and $\exp(E_{\rm nat})=2^{E_{\rm base\,2}}$
--   - encoding: finite-dimensional tensor legs are abstract vector spaces → chosen bases turn them into coordinate arrays and a chosen quotient representative is evaluated; reason: the entanglement-polytope value is invariant under invertible changes of basis and deletion of unused ambient directions
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac698c902a02f2df11dd0671a5d9ca373aed822ae44b7e2640fc152c7d), Theorem 5.4, p.39

import Mathlib
import Definitions.Def_AsymSpecConn_tensorPreorder
import Definitions.Def_AsymSpecConn_Supplement_logValueSet
import Definitions.Def_AsymSpecConn_Supplement_singletonUpperQuantum

set_option autoImplicit false

open scoped NNReal ENNReal

namespace AsymSpecConn.Supplement

/-- **Theorem 5.4** (p.39) of Vrana and Zuiddam, *The asymptotic spectrum of tensors is
connected*, preprint (STOC 2027 submission, version of November 2, 2026,
sha256 85a0b2ac…): for every probability weight `theta` on the legs, the asymptotic extension
of the weighted flattening-rank product equals the singleton upper quantum functional; in
particular that functional is a spectral point.

**Formalization Note** The first equality is pointwise after coercing the finite nonnegative
quantum value to `ℝ≥0∞`, the codomain of the published `Fw`. `theta` ranges over the closed
simplex, so zero weights are included and `0^0=1`. The imported moment-polytope maximum uses
natural entropy; exponentiating it is exactly the source's base-two `2^{E^theta}`. -/
theorem theorem_5_4 {k : ℕ} (hk : 2 ≤ k) (theta : Fin k → ℝ)
    (htheta : IsProbabilityWeight theta) :
    (∀ s : MME.TensorQ ℂ k,
      ((singletonUpperQuantum theta s : ℝ≥0) : ℝ≥0∞) =
        AsymSpecConn.Fw (AsymSpecConn.tensorPreorder ℂ hk)
          (AsymSpecConn.jointlyIrreducibleSet hk) (singletonRankWeight hk theta) s) ∧
    singletonUpperQuantum theta ∈
      AsymSpecConn.Spectrum (MME.TensorQ ℂ k) (AsymSpecConn.tensorPreorder ℂ hk) := by sorry

end AsymSpecConn.Supplement
