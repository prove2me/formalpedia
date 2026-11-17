-- Prove2me | Theorems.Thm_CallCountPOPBR_Supplement_theorem_5_1
-- name    : CallCountPOPBR.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:05:31.647723+00:00
-- url     : https://prove2.me/theorems/5b4caca4-1d75-413b-a631-440acf382567
-- title:
--   Theorem 5.1 — unrestricted abstract realisability
-- statement:
--   An integer sequence $(c_n)_{n\ge0}$ is the invocation-count sequence of an abstract decreasing-argument recursive specification with unrestricted branching if and only if
--
--   $$
--   c_0=1\qquad\text{and}\qquad c_n\ge1\quad\text{for every }n.
--   $$
--
--   Repeated immediate calls are permitted, and the specification need not be computable.
--
--   Differences from the source:
--   - encoding: an abstract rule may repeatedly call any smaller input → a list of smaller natural-number arguments, whose recursively defined natural count is cast to an integer; reason: lists retain multiplicity and order while representing exactly the source model
-- source:
--   Swain, Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and Partial-Observation Reconstruction, STOC 2027 submission (manuscript sha256 79135884…), Theorem 5.1, p.9

import Mathlib
import Definitions.Def_CallCountPOPBR_Supplement_DecSpec

set_option autoImplicit false

namespace CallCountPOPBR.Supplement

/-- **Theorem 5.1 (Unrestricted abstract realisability).** Swain, *Recursive Call-Count Sequences: Structural Realisability, Periodic Branching, and
Partial-Observation Reconstruction*, STOC 2027 submission (manuscript sha256 79135884…), Theorem 5.1, p.9: "A sequence of
integers (c_n)_{n≥0} is realisable by an abstract decreasing-argument recursive specification with
unrestricted branching if and only if c_0 = 1 and c_n ≥ 1 for all n."

Realisable: `c n` is the call count `s.count n` of some decreasing-argument specification `s`
(no bound on the number of calls). -/
theorem theorem_5_1 (c : ℕ → ℤ) :
    (∃ s : DecSpec, ∀ n, c n = (s.count n : ℤ)) ↔ (c 0 = 1 ∧ ∀ n, 1 ≤ c n) := by sorry

end CallCountPOPBR.Supplement
