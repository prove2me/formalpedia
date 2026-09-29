-- Prove2me | Theorems.Thm_FamousTheorems_iscompact_iff_isseqcompact
-- name    : FamousTheorems.iscompact_iff_isseqcompact
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T16:54:49.644093+00:00
-- url     : https://prove2.me/theorems/6afae490-edbb-4293-bbbd-6d03938e6d90
-- title:
--   Sequential compactness equals compactness
-- statement:
--   **Compactness and sequential compactness coincide** in a uniform space with a countable basis. In general topology the two notions are independent -- there are compact spaces that are not sequentially compact and conversely -- and the equivalence holds precisely when enough countability is present, as in metric spaces. That is why analysis can move freely between extracting convergent subsequences and using open covers, while general topology cannot. **Formalization note.** `IsSeqCompact` is the subsequence-extraction property, and the ambient space is uniform with a countably generated uniformity. The result is Mathlib's `isCompact_iff_isSeqCompact`.
-- source:
--   Marked as a named theorem in Mathlib's own docstrings; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem iscompact_iff_isseqcompact :
    ∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X] 
    {s : Set X}, IsCompact s ↔ IsSeqCompact s := by sorry

end FamousTheorems
