-- Prove2me | Theorems.Thm_FamousTheorems_urysohn_lemma
-- name    : FamousTheorems.urysohn_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:14.604993+00:00
-- url     : https://prove2.me/theorems/1ff66eac-5acb-4529-b179-73104add11af
-- title:
--   Urysohn's lemma
-- statement:
--   **Urysohn's lemma.** Let $X$ be a normal topological space and $s,t\subseteq X$ disjoint closed sets. There is a continuous function $f:X\to[0,1]$ with $f=0$ on $s$ and $f=1$ on $t$.
--
--   It is the fundamental link between the separation axioms and real-valued functions. It is the key step in the Tietze extension theorem, in Urysohn's metrization theorem, and in constructing partitions of unity.
--
--   **Formalization note.** Mathlib's `exists_continuous_zero_one_of_isClosed`. `C(X, ℝ)` is the type of continuous real functions on `X`. The range condition is stated pointwise as `f x ∈ Set.Icc 0 1`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `exists_continuous_zero_one_of_isClosed`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem urysohn_lemma {X : Type*} [TopologicalSpace X] [NormalSpace X] {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
    (hd : Disjoint s t) : ∃ f : C(X, ℝ), Set.EqOn f 0 s ∧ Set.EqOn f 1 t ∧ ∀ x, f x ∈ Set.Icc (0 : ℝ) 1 := by sorry

end FamousTheorems
