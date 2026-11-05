-- Prove2me | Theorems.Thm_DHRUniq_lemma_11
-- name    : DHRUniq.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:37:12.99577+00:00
-- url     : https://prove2.me/theorems/065a02c9-add4-4c01-86cf-816ea0b19310
-- title:
--   Lemma 11: (P1′), (P2), (P4) give (P0), (P1), and (E0) under (E2) or (E6′)
-- statement:
--   Let $E$ be a functional satisfying (P1′), (P2) and (P4). Then:
--
--   1. $E$ satisfies (P0) and (P1).
--   2. If $E$ satisfies (E2), then it satisfies (E0).
--   3. If $E$ is nonnegative on states and satisfies (E6′), then it satisfies (E0).
--
--   So the normalization on one Bell pair fixes $E$ on every maximally entangled state, and $E$ vanishes on separable states.
--
--   Differences from the source:
--   - encoding: finite-dimensional Hilbert spaces H^A, H^B → ℂ^a, ℂ^b for finite index types a, b with the standard basis; reason: every finite-dimensional Hilbert space is unitarily isomorphic to such a space
--   - generalization: E is an entanglement measure, hence non-negative (§5.1, p. 8) → nonnegativity is assumed only on the (E6′) branch; reason: clauses 1 and 2 hold without it, so the Lean statement covers the paper's measures and more
--   - generalization: (E6′) for any decomposition → (E6′) for finite decompositions; reason: a weaker hypothesis gives a stronger lemma, and (E6′) for all decompositions implies it
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, Lemma 11, p. 11

import Mathlib
import Definitions.Def_DHRUniq_BipartiteFunctional
import Definitions.Def_DHRUniq_P0
import Definitions.Def_DHRUniq_P1
import Definitions.Def_DHRUniq_P1prime
import Definitions.Def_DHRUniq_P2
import Definitions.Def_DHRUniq_P4
import Definitions.Def_DHRUniq_E0
import Definitions.Def_DHRUniq_E2
import Definitions.Def_DHRUniq_E6prime
import Definitions.Def_WildeQIT_IsDensityOperator

open WildeQIT (IsDensityOperator)

namespace DHRUniq

/-- **Lemma 11** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, Lemma 11, p. 11): "Let `E` be an entanglement measure which satisfies (P1′),
(P2), and (P4). Then `E` satisfies (P0) and (P1). Moreover, if `E` is defined on mixed states and
satisfies either (E2) or (E6′), then (E0) is satisfied."

**Formalization Note** An entanglement measure is non-negative (§5.1, p. 8). Only the (E6′) branch
needs this, so it is assumed there alone: with (E2), `E(σ) ≥ 0` for separable `σ` already follows from
(E2) and (P0). -/
theorem lemma_11 (E : BipartiteFunctional) (h1 : P1prime E) (h2 : P2 E) (h4 : P4 E) :
    (P0 E ∧ P1 E) ∧ (E2 E → E0 E) ∧
      ((∀ ⦃a b : Type⦄ [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
          (σ : Matrix (a × b) (a × b) ℂ), IsDensityOperator σ → 0 ≤ E σ) →
        E6prime E → E0 E) := by sorry

end DHRUniq
