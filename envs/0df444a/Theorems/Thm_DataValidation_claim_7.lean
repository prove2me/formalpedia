-- Prove2me | Theorems.Thm_DataValidation_claim_7
-- name    : DataValidation.claim_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:46:54.486195+00:00
-- url     : https://prove2.me/theorems/151f9fb8-81da-4e95-8505-ffaff569d054
-- title:
--   Claim 7 — deleting an edge keeps the rest of the transitive reduction
-- statement:
--   Let $E$ be an acyclic edge set and $e\in E$. Then
--
--   $$R(E)\setminus\{e\}\subseteq R(E\setminus\{e\}).$$
--
--   So an edge that may be probed stays probable after another edge has been removed.
--
--   Differences from the source: none.
-- source:
--   Tinguely, van der Heijden, Approximation and Hardness for the Data Validation Problem, arXiv:2611.06773 (sha256 6595f819…), Claim 7, p.6

import Definitions.Def_DataValidation_transReduction

set_option autoImplicit false

namespace DataValidation

/-- **Claim 7** of arXiv:2611.06773 (sha256 6595f819…), p.6: for any acyclic edge set `E` and any
edge `e ∈ E`, `R(E) ∖ {e} ⊆ R(E ∖ {e})`. -/
theorem claim_7 {V : Type*} [DecidableEq V] (E : Finset (V × V)) (hE : IsAcyclic E) (e : V × V)
    (he : e ∈ E) : (transReduction E).erase e ⊆ transReduction (E.erase e) := by sorry

end DataValidation
