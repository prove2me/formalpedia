-- Prove2me | Theorems.Thm_Erdos9796Mission_critical_cover_tight_center_exists
-- name    : Erdos9796Mission.critical_cover_tight_center_exists
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-12T20:42:41.319543+00:00
-- url     : https://prove2.me/theorems/e2bd54c1-b5d5-4e06-96de-869444dd3273
-- title:
--   Critical cover yields a tight center inside the set
-- statement:
--   Let $A$ be a finite set of points in the Euclidean plane. Suppose every point $x \in A$ is covered by a critical circle: there are a center $p \in A$ with $p \ne x$ and a radius $r > 0$ with $\mathrm{dist}(p, x) = r$ such that exactly four points of $A$ lie at distance $r$ from $p$, and no other positive radius at $p$ carries four or more points of $A$. Then for every $x \in A$ there exist a center $p_0 \in A$ and a radius $r_0 > 0$ with
--
--   $$\mathrm{dist}(p_0, x) = r_0, \quad |\{q \in A : \mathrm{dist}(p_0, q) = r_0\}| = 4,$$
--
--   and $r_0$ is the unique positive radius at $p_0$ whose distance class in $A$ has at least four points.
--
--   This packages each covering witness as a tight center inside $A$. It is the combinatorial selection interface used by the cardinality reduction of the critical-radius cover.
--
--   **Formalization Note** Lean records non-membership of the center by $p \in A.\mathrm{erase}\ x$; the conclusion weakens this to $p_0 \in A$.
-- source:
--   Decomposition of Erdos9796Mission.critical_radius_cover_card_le_nine (open frontier leaf of Prove2Me mission Erdős Problems 97 and 96), developed for this submission. Original open descent statement: https://github.com/mysticflounder/erdos-97-96-formalization/blob/757d852766f377f7c1a0ffeeef6d3526bc0cb7a4/lean/Erdos9796Proof/P97/RemovableVertexAxiom/Base.lean#L53

import Definitions.Def_Erdos9796Mission
open Erdos9796Mission
open Classical

theorem Erdos9796Mission.critical_cover_tight_center_exists
    (A : Finset Plane)
    (hcover : ∀ x ∈ A, ∃ p ∈ A.erase x, ∃ r : ℝ,
      0 < r ∧ dist p x = r ∧
      (A.filter (fun q => dist p q = r)).card = 4 ∧
      ∀ s : ℝ, 0 < s →
        4 ≤ (A.filter (fun q => dist p q = s)).card → s = r)
    (x : Plane) (hx : x ∈ A) :
    ∃ p₀ ∈ A, ∃ r₀ : ℝ,
      0 < r₀ ∧ dist p₀ x = r₀ ∧
      (A.filter (fun q => dist p₀ q = r₀)).card = 4 ∧
      ∀ s : ℝ, 0 < s →
        4 ≤ (A.filter (fun q => dist p₀ q = s)).card → s = r₀ := by sorry
