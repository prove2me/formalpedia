-- Prove2me | Theorems.Thm_FamousTheorems_borel_isomorphism_theorem
-- name    : FamousTheorems.borel_isomorphism_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:23.084277+00:00
-- url     : https://prove2.me/theorems/0067059d-6b52-40f7-9f7e-ce7cb2939f05
-- title:
--   The Borel isomorphism theorem
-- statement:
--   **Kuratowski's Borel isomorphism theorem.** Any two uncountable standard Borel spaces are Borel isomorphic: there is a bijection between them that is measurable with measurable inverse.
--
--   Standard Borel spaces are measurable spaces coming from Polish spaces, such as $\mathbb R^n$, $[0,1]$, the Cantor space and separable Banach spaces. Up to isomorphism there is exactly one uncountable standard Borel space, so as measurable spaces $\mathbb R$ and $[0,1]^{\mathbb N}$ are indistinguishable. Together with the countable case this classifies standard Borel spaces by cardinality.
--
--   **Formalization note.** Mathlib's `PolishSpace.measurableEquivOfNotCountable`, a construction, so the statement asserts that the type `MeasurableEquiv α β` of measurable equivalences is nonempty. `StandardBorelSpace α` says that the $\sigma$-algebra is the Borel $\sigma$-algebra of some Polish topology.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `PolishSpace.measurableEquivOfNotCountable`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem borel_isomorphism_theorem {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [StandardBorelSpace α] [StandardBorelSpace β]
    (hα : ¬Countable α) (hβ : ¬Countable β) :
    Nonempty (MeasurableEquiv α β) := by sorry

end FamousTheorems
