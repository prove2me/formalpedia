-- Prove2me | Theorems.Thm_DHRUniq_lemma_10
-- name    : DHRUniq.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:34:48.475299+00:00
-- url     : https://prove2.me/theorems/6c331ad6-74ed-4356-9dc7-e0f5f0983850
-- title:
--   Lemma 10: asymptotic additivity is equivalent to additivity
-- statement:
--   Let $E$ be a functional that does not distinguish isomorphic local spaces. Then (E4′) is equivalent to (E4), and (P4′) is equivalent to (P4).
--
--   Thus a measure that is additive on tensor powers in the limit is exactly additive on them.
--
--   Differences from the source:
--   - encoding: E is a functional on pure states → E is a real function on all matrices over finite bipartite index types; reason: only its values at |ψ⟩⟨ψ| for unit ψ are read, and every functional on pure states extends to such a function
--   - encoding: finite-dimensional Hilbert spaces H^A, H^B → ℂ^a, ℂ^b for finite index types a, b with the standard basis; reason: every finite-dimensional Hilbert space is unitarily isomorphic to such a space
--   - reading: the proof treats (ϱ^⊗m)^⊗n and ϱ^⊗mn as equal, "equivalent density matrices on products of isomorphic local spaces" → the hypothesis LocallyInvariant E; reason: the two states are matrices over different index types in Lean, and the paper's identification of isomorphic spaces (with the standing assumption (E2′′), p. 8) must be stated to say anything about them
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, Lemma 10, p. 10

import Mathlib
import Definitions.Def_DHRUniq_BipartiteFunctional
import Definitions.Def_DHRUniq_LocallyInvariant
import Definitions.Def_DHRUniq_E4
import Definitions.Def_DHRUniq_E4prime
import Definitions.Def_DHRUniq_P4
import Definitions.Def_DHRUniq_P4prime

namespace DHRUniq

/-- **Lemma 10** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, Lemma 10, p. 10): "(E4′) is equivalent to (E4) and (P4′) is equivalent to
(P4)."

**Formalization Note** `LocallyInvariant E` is the paper's identification of isomorphic local spaces,
used in its proof ("`(ϱ^{⊗m})^{⊗n} = ϱ^{⊗mn}` where the equality relates equivalent density matrices
on products of isomorphic local spaces"). In Lean those two states are matrices over different index
types, and without the hypothesis the lemma fails: nothing would relate `E` on the two types. -/
theorem lemma_10 (E : BipartiteFunctional) (hE : LocallyInvariant E) :
    (E4prime E ↔ E4 E) ∧ (P4prime E ↔ P4 E) := by sorry

end DHRUniq
