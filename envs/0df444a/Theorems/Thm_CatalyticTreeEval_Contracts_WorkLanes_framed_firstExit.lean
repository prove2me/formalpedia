-- Prove2me | Theorems.Thm_CatalyticTreeEval_Contracts_WorkLanes_framed_firstExit
-- name    : CatalyticTreeEval.Contracts.WorkLanes.framed_firstExit
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-14T06:41:49.993181+00:00
-- url     : https://prove2.me/theorems/a261ad10-3264-4818-87b2-6bb5752dc337
-- title:
--   Whole-subroutine native work-lane compilation with exact transient resources
-- statement:
--   Fix a native source machine A, K lanes and a lane j<K. Suppose an initialized physical tape represents the source work tape at addresses b+(K+1)p+j and has a true origin marker only at row zero. If A first halts after T transitions with a work-head bound B, catalyst-head envelope and writable footprint, then the actual fixed finite compiled machine first halts after $$T(2(K-j)+1+K)$$ transitions. Every intermediate native work head lies in $[b,b+(K+1)B)$, the catalyst envelope is retained, and the writable work footprint is mapped by the lane addressing. Every inactive work lane is preserved exactly. The endpoint represents the exact source endpoint, including output, catalyst and heads. The table is fixed before input, tape contents, workspace width and T; origin initialization is an explicit precondition.
-- source:
--   Infrastructure for Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, native uniform arithmetic and finite-control subroutine composition.

import Definitions.Def_CatalyticTreeEval_WorkLaneContracts

namespace CatalyticTreeEval.Contracts.WorkLanes

theorem framed_firstExit (A : CatalyticTreeEval.Main.Machine) (lanes : ℕ) (lane : Fin lanes) (base : ℕ)
    (input : List Bool) (source target : CatalyticMatching.General.Configuration A)
    (physical : ℕ → Bool) (T : ℕ) (E : CatalyticTreeEval.Contracts.Envelope)
    (F : CatalyticTreeEval.Contracts.Footprint)
    (hi : source.inputHead ≤ input.length + 1)
    (hc : source.catalystHead ≤ source.catalyst.length)
    (origin : CatalyticTreeEval.Contracts.WorkLanes.OriginTrack lanes base physical)
    (workMatches : CatalyticTreeEval.Contracts.WorkLanes.Matches lane base source.work physical)
    (H : CatalyticTreeEval.Contracts.FirstExit (A.step input)
      (fun _ d => E.Contains d ∧ CatalyticTreeEval.Contracts.SameOutside F source d)
      {d | d.state = none} source target T) :
    ∃ updated : ℕ → Bool,
      CatalyticTreeEval.Contracts.WorkLanes.OriginTrack lanes base updated ∧
      CatalyticTreeEval.Contracts.WorkLanes.Matches lane base target.work updated ∧
      CatalyticTreeEval.Contracts.WorkLanes.Inactive lane base physical updated ∧
      CatalyticTreeEval.Contracts.FirstExit
        ((CatalyticTreeEval.Contracts.WorkLanes.machine A lanes lane).step input)
        (fun _ e => (CatalyticTreeEval.Contracts.WorkLanes.liftedEnvelope lanes base E).Contains e ∧
          CatalyticTreeEval.Contracts.SameOutside
            (CatalyticTreeEval.Contracts.WorkLanes.liftedFootprint lane base F)
            (CatalyticTreeEval.Contracts.WorkLanes.embed A lanes lane base source physical) e)
        {e | e.state = none}
        (CatalyticTreeEval.Contracts.WorkLanes.embed A lanes lane base source physical)
        (CatalyticTreeEval.Contracts.WorkLanes.embed A lanes lane base target updated)
        (T * CatalyticTreeEval.Contracts.WorkLanes.macroTime lane) := by
  sorry

end CatalyticTreeEval.Contracts.WorkLanes
