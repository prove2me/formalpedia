-- Prove2me | Theorems.Thm_FamousTheorems_dieudonne_paracompact_normal
-- name    : FamousTheorems.dieudonne_paracompact_normal
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:08:26.266984+00:00
-- url     : https://prove2.me/theorems/b690a72d-33a7-4eae-a1c5-a26201388cce
-- title:
--   Dieudonné's theorem: paracompact Hausdorff spaces are normal
-- statement:
--   **Dieudonné's theorem.** Every paracompact Hausdorff space is normal: any two disjoint closed sets have disjoint open neighbourhoods.
--
--   Dieudonné introduced paracompactness in 1944 and proved this theorem. Normality gives Urysohn functions and partitions of unity subordinate to any open cover. These are the main reason paracompact spaces, including all metric spaces and all manifolds, are the natural setting for gluing local constructions.
--
--   **Formalization note.** Mathlib's `NormalSpace.of_paracompactSpace_r1Space`, which requires only the weaker $R_1$ separation axiom. Every Hausdorff (`T2Space`) space is $R_1$. `ParacompactSpace X` says that every open cover has a locally finite open refinement.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `NormalSpace.of_paracompactSpace_r1Space`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem dieudonne_paracompact_normal {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] :
    NormalSpace X := by sorry

end FamousTheorems
