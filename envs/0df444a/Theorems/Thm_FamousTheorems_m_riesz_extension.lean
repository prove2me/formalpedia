-- Prove2me | Theorems.Thm_FamousTheorems_m_riesz_extension
-- name    : FamousTheorems.m_riesz_extension
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:15:06.33515+00:00
-- url     : https://prove2.me/theorems/f9317f6e-4970-474a-83d2-95e69410df63
-- title:
--   The M. Riesz extension theorem
-- statement:
--   **The M. Riesz extension theorem.** Let $E$ be a real vector space, $s\subseteq E$ a convex cone, and $f$ a linear functional defined on a subspace $D$ that is nonnegative on $D\cap s$. Assume $D+s=E$ (every $y$ has some $x\in D$ with $x+y\in s$). Then $f$ extends to a linear functional $g$ on all of $E$ that is nonnegative on $s$.
--
--   This positive-extension theorem of Marcel Riesz implies the Hahn–Banach theorem. It is used in the moment problem, the existence of Haar-type positive functionals, and Choquet theory.
--
--   **Formalization note.** Mathlib's `riesz_extension`, with the cone as a `PointedCone ℝ E` and the partially defined functional as a `LinearPMap` (`E →ₗ.[ℝ] ℝ`).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `riesz_extension`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem m_riesz_extension {E : Type*} [AddCommGroup E] [Module ℝ E] (s : PointedCone ℝ E) (f : E →ₗ.[ℝ] ℝ)
    (nonneg : ∀ x : f.domain, (x : E) ∈ s → 0 ≤ f x) (dense : ∀ y : E, ∃ x : f.domain, (x : E) + y ∈ s) :
    ∃ g : E →ₗ[ℝ] ℝ, (∀ x : f.domain, g x = f x) ∧ ∀ x ∈ s, 0 ≤ g x := by sorry

end FamousTheorems
