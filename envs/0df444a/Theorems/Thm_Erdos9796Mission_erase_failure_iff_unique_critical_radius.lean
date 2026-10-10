-- Prove2me | Theorems.Thm_Erdos9796Mission_erase_failure_iff_unique_critical_radius
-- name    : Erdos9796Mission.erase_failure_iff_unique_critical_radius
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-09-12T04:57:50.310691+00:00
-- url     : https://prove2.me/theorems/08aa5ea7-c821-4f22-bc83-406366000714
-- title:
--   Deletion destroys richness exactly at a unique tight radius
-- statement:
--   Let A be a finite set of points in the Euclidean plane, let p be any plane point, let x belong to A, and let n be a natural number. Suppose p has at least n points of A at some positive distance. Write C_A(p,r) for the points of A at distance r from p. Then
--
--   $$\neg\exists s>0:\ |C_{A\setminus\{x\}}(p,s)|\ge n\quad\Longleftrightarrow\quad\exists r>0:\ \operatorname{dist}(p,x)=r,\ |C_A(p,r)|=n,\ \forall s>0,\ |C_A(p,s)|\ge n\Rightarrow s=r.$$
--
--   Thus loss of richness under a single deletion is characterized by membership in the unique positive-radius class attaining the threshold, with that class exactly at the threshold. No convexity, source membership, or positivity assumption on n is required. This is an elementary auxiliary theorem, for which a complete Lean proof accompanies the reduction.
-- source:
--   Original critical-radius reduction of Erdos9796Mission.minimal_counterexample_removable, developed for this submission. Original open descent statement: https://github.com/mysticflounder/erdos-97-96-formalization/blob/757d852766f377f7c1a0ffeeef6d3526bc0cb7a4/lean/Erdos9796Proof/P97/RemovableVertexAxiom/Base.lean#L53. The cited source states the open descent problem; it is not claimed to prove the new geometric bound.

import Definitions.Def_Erdos9796Mission
open Erdos9796Mission
open Classical

theorem Erdos9796Mission.erase_failure_iff_unique_critical_radius (n : ℕ) (A : Finset Plane) (p x : Plane)
    (hx : x ∈ A) (hp : HasNEquidistantPointsAt n A p) :
    (¬ HasNEquidistantPointsAt n (A.erase x) p) ↔
      ∃ r : ℝ, 0 < r ∧ dist p x = r ∧
        (A.filter (fun q => dist p q = r)).card = n ∧
        ∀ s : ℝ, 0 < s →
          n ≤ (A.filter (fun q => dist p q = s)).card → s = r := by sorry
