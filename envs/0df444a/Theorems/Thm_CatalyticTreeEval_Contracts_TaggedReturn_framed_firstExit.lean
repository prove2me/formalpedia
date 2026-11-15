-- Prove2me | Theorems.Thm_CatalyticTreeEval_Contracts_TaggedReturn_framed_firstExit
-- name    : CatalyticTreeEval.Contracts.TaggedReturn.framed_firstExit
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-14T08:16:17.82954+00:00
-- url     : https://prove2.me/theorems/8a8c86c0-27a0-4dfa-93f3-49765e19b00c
-- title:
--   Exact native subroutine calls retaining finite continuation context
-- statement:
--   Fix a native child machine and a finite continuation context, both before the input. If the child first halts after T transitions and satisfies a head envelope and a writable-memory frame at every prefix, the product controller reaches the live return port carrying that context after exactly T actual native transitions. The source head envelope and writable footprint hold unchanged throughout. The context is stored in fixed finite control, with no additional work cells. A separate physical transition leaves the return port; it is not omitted from later caller dispatch costs. The result provides a charged native callback interface for replay and uniform machine composition.
-- source:
--   Native composition infrastructure for Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, subroutine and replay hosts.

import Definitions.Def_CatalyticTreeEval_TaggedReturn

open CatalyticMatching.General

namespace CatalyticTreeEval.Contracts.TaggedReturn

theorem framed_firstExit (A : Machine) (tags : ℕ) (tag : Fin (tags + 1))
    (input : List Bool) (c d : Configuration A) (T : ℕ) (E : Envelope) (F : Footprint)
    (H : FirstExit (A.step input) (fun _ e => E.Contains e ∧ SameOutside F c e)
      {e | e.state = none} c d T) :
    FirstExit ((machine A tags).step input)
      (fun _ e => E.Contains e ∧ SameOutside F (embed A tags tag c) e)
      {e | e.state = some (returned A tags tag)}
      (embed A tags tag c) (embed A tags tag d) T := by
  sorry

end CatalyticTreeEval.Contracts.TaggedReturn
