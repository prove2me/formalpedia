-- Prove2me | Theorems.Thm_FamousTheorems_los_vaught_test
-- name    : FamousTheorems.los_vaught_test
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:57:36.658387+00:00
-- url     : https://prove2.me/theorems/3cc440c7-cae7-4896-9421-fc0e4ffdfe73
-- title:
--   The Łoś–Vaught test
-- statement:
--   **The Łoś–Vaught test.** Let $T$ be a satisfiable theory in a language $L$ with no finite models, and let $\kappa$ be an infinite cardinal with $|L|\le\kappa$. If $T$ is $\kappa$-categorical (all models of $T$ of cardinality $\kappa$ are isomorphic), then $T$ is complete.
--
--   This is the simplest method of proving completeness of first-order theories. It shows, for example, that the theory of dense linear orders without endpoints ($\aleph_0$-categorical) and the theory of algebraically closed fields of fixed characteristic (categorical in uncountable cardinals) are complete.
--
--   **Formalization note.** Mathlib's `Cardinal.Categorical.isComplete`. The language lives in universes `u, v`, the cardinal `κ : Cardinal.{w}` in a possibly different universe, and `Cardinal.lift` compares `L.card` with `κ`. "No finite models" is stated for models in universe `max u v`, and `T.IsComplete` means $T$ is satisfiable and every sentence or its negation is a consequence of $T$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Cardinal.Categorical.isComplete`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe u v w

theorem los_vaught_test {L : FirstOrder.Language.{u, v}} (κ : Cardinal.{w}) (T : L.Theory) (h : κ.Categorical T)
    (h1 : Cardinal.aleph0 ≤ κ) (h2 : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) (hS : T.IsSatisfiable)
    (hT : ∀ M : FirstOrder.Language.Theory.ModelType.{u, v, max u v} T, Infinite M) : T.IsComplete := by sorry

end FamousTheorems
