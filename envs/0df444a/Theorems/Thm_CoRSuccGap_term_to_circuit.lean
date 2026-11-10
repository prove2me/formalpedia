-- Prove2me | Theorems.Thm_CoRSuccGap_term_to_circuit
-- name    : CoRSuccGap.term_to_circuit
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:48:25.769224+00:00
-- url     : https://prove2.me/theorems/3e337799-995a-4b33-aec9-a20e7791794c
-- title:
--   Proof of Theorem 1.1 — a term is a circuit without sharing: every term $T$ is computed by a circuit with $\#_{;}(T)$ composition gates
-- statement:
--   For every CoR term $T$ over a signature $\sigma$ there is a relational circuit $C$ over $\sigma$ such that
--
--   $$
--   [\![C]\!]^{\mathcal M}=[\![T]\!]^{\mathcal M}\ \text{ for every structure }\mathcal M,\qquad g_{;}(C)=\#_{;}(T).
--   $$
--
--   This is the step "a term is a circuit without sharing" that transfers the circuit bound of Theorem 1.1 to terms.
--
--   **Formalization Note** "Every structure" means every domain `D : Type` (finite or not, empty or not) and every interpretation of `σ`.
--
--   Differences from the source:
--   - reading: "A term is a circuit without sharing, so the same bound holds for its number of compositions" → every term is computed, on every structure, by a circuit whose number of composition gates equals its number of compositions; reason: the sentence's content made explicit; it is exactly what transfers the bound
-- source:
--   Y. Uezato, Y. Nakamura, An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of Relations, arXiv:2609.26778 (held version, sha256 5ad6337daad55bcf6132960d4744d07ff7d67ef2a9aef456f3e3b54ff623c9b6), proof of Theorem 1.1, p.22 (PDF 24)

import Mathlib
import Definitions.Def_CoRSuccGap_Term
import Definitions.Def_CoRSuccGap_Circuit

set_option autoImplicit false

namespace CoRSuccGap

/-- **A term is a circuit without sharing** (proof of Theorem 1.1). Uezato–Nakamura, *An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of
Relations*, arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), proof of
Theorem 1.1, p.22 (PDF 24): "A term is a circuit without sharing, so the same bound holds for its
number of compositions." Every CoR term `T` is computed by a relational circuit with exactly
#;(T) composition gates, on every structure.

**Formalization Note.** The circuit agrees with `T` on every structure with domain in `Type`
(finite or infinite, empty or not), and `numCompGates` counts every gate of the circuit. -/
theorem term_to_circuit {σ : Type*} (T : Term σ) :
    ∃ C : Circuit σ, (∀ (D : Type) (M : σ → D → D → Prop), C.eval M = T.eval M) ∧
      C.numCompGates = T.numComp := by sorry

end CoRSuccGap
