-- Prove2me | Theorems.Thm_ConstDepthUnitary_exact_and_or
-- name    : ConstDepthUnitary.exact_and_or
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:47:52.764269+00:00
-- url     : https://prove2.me/theorems/d6f0e760-e5d1-451f-9d9f-b83783c627dc
-- title:
--   Lemma 6.4 — exact AND and OR in constant depth
-- statement:
--   There are universal constants $d_0$ and $C$ such that for every $r\ge1$, each of the gates
--   $$|x\rangle|b\rangle\mapsto|x\rangle\bigl|b\oplus\textstyle\bigwedge_i x_i\bigr\rangle,\qquad|x\rangle|b\rangle\mapsto|x\rangle\bigl|b\oplus\textstyle\bigvee_i x_i\bigr\rangle$$
--   on $r$ controls and one target has a clean exact circuit with fan-out, of depth at most $d_0$, with at most $Cr\log_2r$ ancillas.
--
--   The paper cites this result from Takahashi and Tani (2016). It is the basic classical computation step of the constant-depth constructions.
--
--   Differences from the source:
--   - reading: "AND and OR gates on r qubits" → r input qubits and one target; reason: a target counted in the r changes only the constant
--   - reading: "computed exactly" → a clean exact implementation: ancillas return to 0 on every input; reason: Algorithm 2, Step 3 and the reflection of Theorem 7.1 need this
--   - encoding: constants hidden in O(·) → an existential constant quantified before all data; reason: the paper's constants are universal
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 6.4, p.36

import Mathlib
import Definitions.Def_ConstDepthUnitary_Circuit
import Definitions.Def_ConstDepthUnitary_CleanlyImplements
import Definitions.Def_ConstDepthUnitary_xorOracle

namespace ConstDepthUnitary

/-- Lemma 6.4 (exact AND and OR gates, [TT16]): the AND and OR of `r` bits, computed into a target qubit, have clean exact
circuits with fan-out of universally bounded depth and `O(r log r)` ancillas.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 6.4, p.36. -/
theorem exact_and_or :
    ∃ (d₀ : ℕ) (C : ℝ), ∀ r : ℕ, 1 ≤ r →
      (∃ (m : ℕ) (D : Circuit ((Fin r ⊕ Unit) ⊕ Fin m)),
        (m : ℝ) ≤ C * r * Real.logb 2 r ∧ D.depth ≤ d₀ ∧ CleanlyImplements D (xorOracle andFn)) ∧
      (∃ (m : ℕ) (D : Circuit ((Fin r ⊕ Unit) ⊕ Fin m)),
        (m : ℝ) ≤ C * r * Real.logb 2 r ∧ D.depth ≤ d₀ ∧ CleanlyImplements D (xorOracle orFn)) := by sorry

end ConstDepthUnitary
