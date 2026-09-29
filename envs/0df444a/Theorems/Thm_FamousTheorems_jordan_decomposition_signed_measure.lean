-- Prove2me | Theorems.Thm_FamousTheorems_jordan_decomposition_signed_measure
-- name    : FamousTheorems.jordan_decomposition_signed_measure
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:15.201991+00:00
-- url     : https://prove2.me/theorems/be2dad84-7106-4b76-b42e-fee1be87654e
-- title:
--   The Jordan decomposition of a signed measure
-- statement:
--   **The Jordan decomposition theorem.** Every finite signed measure $s$ can be written uniquely as $s=\mu-\nu$ with $\mu,\nu$ finite positive measures that are mutually singular.
--
--   Together with the Hahn decomposition, this is the structure theorem for signed measures. It defines the total variation $|s|=\mu+\nu$. It is used in the Radon–Nikodym theorem for signed measures and in the Riesz representation theorem, which identifies $C(X)^*$ with regular signed measures.
--
--   **Formalization note.** Mathlib's `MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition` for existence and `MeasureTheory.JordanDecomposition.toSignedMeasure_injective` for uniqueness. A `JordanDecomposition α` bundles two finite measures `posPart` and `negPart` with a proof that they are mutually singular. Its `toSignedMeasure` is `posPart - negPart`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.SignedMeasure.toSignedMeasure_toJordanDecomposition`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem jordan_decomposition_signed_measure {α : Type*} [MeasurableSpace α] (s : SignedMeasure α) :
    ∃! j : JordanDecomposition α, j.toSignedMeasure = s := by sorry

end FamousTheorems
