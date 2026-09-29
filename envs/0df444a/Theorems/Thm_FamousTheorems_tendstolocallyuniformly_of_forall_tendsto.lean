-- Prove2me | Theorems.Thm_FamousTheorems_tendstolocallyuniformly_of_forall_tendsto
-- name    : FamousTheorems.tendstolocallyuniformly_of_forall_tendsto
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:30.495982+00:00
-- url     : https://prove2.me/theorems/b2d933e2-2398-4b7f-b2c1-5bbf0520d051
-- title:
--   Dini's theorem
-- statement:
--   **Dini's theorem.** A monotone sequence of continuous functions converging pointwise to a continuous limit converges locally uniformly. Monotonicity upgrades pointwise convergence to uniform — normally a strictly stronger mode — provided the limit is continuous. Both hypotheses are needed: $x^n$ on $[0,1]$ is monotone with discontinuous limit and fails, and dropping monotonicity allows escaping bumps. The mechanism is compactness: the sets where the gap exceeds $\varepsilon$ are nested, closed and eventually empty pointwise, so one of them is empty. It is the standard shortcut for establishing uniform convergence without estimating the tail. **Formalization note.** The conclusion is `TendstoLocallyUniformly`, which is uniform convergence on a neighbourhood of each point. The result is Mathlib's `Monotone.tendstoLocallyUniformly_of_forall_tendsto`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem tendstolocallyuniformly_of_forall_tendsto :
    ∀ {ι : Type u_1} {α : Type u_2} {G : Type u_3} [inst : Preorder ι] 
    [inst_1 : TopologicalSpace α] [inst_2 : NormedAddCommGroup G] [inst_3 : Lattice G] [HasSolidNorm G] 
    [IsOrderedAddMonoid G] {F : ι → α → G} {f : α → G}, 
    (∀ (i : ι), Continuous (F i)) → 
    Monotone F → 
    Continuous f → (∀ (x : α), Tendsto (fun x_1 => F x_1 x) atTop (𝓝 (f x))) → TendstoLocallyUniformly F f atTop := by sorry

end FamousTheorems
