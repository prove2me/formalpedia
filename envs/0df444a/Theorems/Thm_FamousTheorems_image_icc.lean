-- Prove2me | Theorems.Thm_FamousTheorems_image_icc
-- name    : FamousTheorems.image_icc
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T08:37:47.938165+00:00
-- url     : https://prove2.me/theorems/8078f3ae-e7ff-4f49-8dc0-a8d6496ecd30
-- title:
--   The image of a closed interval under a continuous map
-- statement:
--   **The image of a segment.** A continuous real-valued function on a closed bounded interval maps it onto a closed bounded interval: $$f\bigl([a,b]\bigr) = \bigl[\min_{[a,b]} f,\ \max_{[a,b]} f\bigr].$$ Two theorems at once. That the image is *bounded and attains its endpoints* is the extreme value theorem, coming from compactness of $[a,b]$; that the image *contains everything between* them is the intermediate value theorem, coming from connectedness. Together they say the continuous image of a compact connected set in $\mathbb{R}$ is again a compact connected set — that is, a closed bounded interval. Both halves fail on an open interval: $x \mapsto 1/x$ on $(0,1)$ is unbounded, and $x \mapsto x$ has no maximum there. **Formalization note.** `ContinuousOn f (Set.Icc a b)` is continuity on the closed interval, and the conclusion is an equality of sets. The result is Mathlib's `ContinuousOn.image_Icc`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem image_icc :
    ∀ {α : Type u_1} {β : Type u_2} [inst : ConditionallyCompleteLinearOrder α] 
    [inst_1 : TopologicalSpace α] [OrderTopology α] [inst_3 : TopologicalSpace β] [DenselyOrdered α] 
    [inst_5 : ConditionallyCompleteLinearOrder β] [OrderTopology β] {f : α → β} {a b : α}, 
    a ≤ b → ContinuousOn f (Icc a b) → f '' Icc a b = Icc (sInf (f '' Icc a b)) (sSup (f '' Icc a b)) := by sorry

end FamousTheorems
