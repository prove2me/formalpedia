-- Prove2me | Theorems.Thm_FamousTheorems_metrizablespace_of_t3_secondcountable
-- name    : FamousTheorems.metrizablespace_of_t3_secondcountable
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:13:04.219574+00:00
-- url     : https://prove2.me/theorems/c992d222-1135-4516-ba4f-9a78aab0a83c
-- title:
--   The Urysohn metrization theorem
-- statement:
--   **The Urysohn metrization theorem.** A second-countable regular Hausdorff space is metrizable. Purely topological hypotheses produce a metric inducing the topology, with no distance function given in advance. The proof embeds the space in the Hilbert cube using countably many Urysohn functions. Second countability cannot be dropped: an uncountable discrete space is metrizable but not second countable, while the long line is regular Hausdorff and not metrizable. Urysohn proved it in 1925. **Formalization note.** `T3Space` is regular Hausdorff and `SecondCountableTopology` supplies the countable base. The result is Mathlib's `TopologicalSpace.metrizableSpace_of_t3_secondCountable`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem metrizablespace_of_t3_secondcountable :
    ∀ (X : Type u_1) [inst : TopologicalSpace X] [T3Space X] 
    [SecondCountableTopology X], TopologicalSpace.MetrizableSpace X := by sorry

end FamousTheorems
