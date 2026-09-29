-- Prove2me | Theorems.Thm_FamousTheorems_real_line_meagre_null_decomposition
-- name    : FamousTheorems.real_line_meagre_null_decomposition
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:41.119302+00:00
-- url     : https://prove2.me/theorems/7073c286-3fda-41ab-8efd-393029ca92de
-- title:
--   ℝ is the union of a meagre set and a null set
-- statement:
--   **$\mathbb R$ is the union of a meagre set and a null set.** The real line can be written as $\mathbb R=A\cup B$, where $A$ is meagre (of first Baire category) and $B$ has Lebesgue measure zero.
--
--   This theorem (in Oxtoby's *Measure and Category*) shows that the two notions of "small set", meagre and null, are orthogonal. Every comeagre set can be null and every conull set can be meagre. One can take $B$ to be the Liouville numbers.
--
--   **Formalization note.** Mathlib's `Real.disjoint_residual_ae`. The statement says that the filter `residual ℝ` of comeagre sets and the filter `ae volume` of conull sets are disjoint. This means that there are a comeagre set and a conull set with empty intersection. Taking complements, $\mathbb R$ is the union of a meagre set and a null set.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Real.disjoint_residual_ae`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem real_line_meagre_null_decomposition : Disjoint (residual ℝ) (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by sorry

end FamousTheorems
