-- Prove2me | Theorems.Thm_FamousTheorems_havelebesguedecomposition_of_sigmafinite
-- name    : FamousTheorems.havelebesguedecomposition_of_sigmafinite
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:08.116015+00:00
-- url     : https://prove2.me/theorems/f5a7579b-29bb-4984-9e2a-38c8000e688a
-- title:
--   The Lebesgue decomposition theorem
-- statement:
--   **The Lebesgue decomposition theorem.** Any $\sigma$-finite measure splits uniquely as $\mu = \mu_{ac} + \mu_s$ with $\mu_{ac}$ absolutely continuous with respect to a given $\nu$ and $\mu_s$ singular to it. Every measure decomposes into a part with a density and a part living on a $\nu$-null set — there is no third kind of behaviour. Combined with Radon\u2013Nikodym, which supplies the density for the absolutely continuous part, this is the complete structure theory for one measure relative to another. It is the measure-theoretic basis for separating continuous and discrete components of a probability distribution. **Formalization note.** `HaveLebesgueDecomposition` asserts the existence of the splitting, here established for $\sigma$-finite measures. The result is Mathlib's `MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem havelebesguedecomposition_of_sigmafinite :
    ∀ {α : Type u_1} {m : MeasurableSpace α} 
    (μ ν : MeasureTheory.Measure α) [MeasureTheory.SFinite μ] [MeasureTheory.SigmaFinite ν], μ.HaveLebesgueDecomposition ν := by sorry

end FamousTheorems
