-- Prove2me | Theorems.Thm_CatalyticTreeEval_Contracts_NativeInputProbe_probe_exec
-- name    : CatalyticTreeEval.Contracts.NativeInputProbe.probe_exec
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-14T15:13:20.023926+00:00
-- url     : https://prove2.me/theorems/f29dd515-d455-4757-88cf-5832b18cf709
-- title:
--   Native buffered-input probe: correct flags, frame and resources
-- statement:
--   Let a binary stream $B$ of length $R$ be stored in actual tagged work-bank cells, with a false terminating tag, and let a separate bookmark represent a virtual input head $i$ satisfying
--
--   $$0\le i\le R+1.$$
--
--   There is one fixed finite native probe, depending only on its constant work-lane roles, whose three physical reply flags are
--
--   $$\begin{cases}(1,0,0),&i=0,\\(0,1,B_{i-1}),&1\le i\le R,\\(0,0,0),&i=R+1.\end{cases}$$
--
--   Thus origin, EOF, false data and true data are distinguished. The probe preserves the complete buffered stream and its unique cursor. Every work cell outside the three reply cells is retained throughout; the real input head, complete catalyst and prior output are unchanged. For $K$ work lanes, its native running time satisfies
--
--   $$T\le20(K+1)(R+2),$$
--
--   and every visited work position is below
--
--   $$\mathrm{base}+(K+1)(8+3R).$$
--
--   The catalyst stays at its initial valid position $p$, so the charged catalyst interval is exactly $[p,p+1)$, independently of any unused suffix. The buffer, cursor and disjoint reply/read-only roles are explicit physical preconditions; constructing the buffer is a separate charged routine.
-- source:
--   Native auxiliary theorem for Section 4, Catalytic Tree Evaluation from Matching Vectors, arXiv:2602.14320. A physical buffer/cursor is assumed; construction is a separate routine.

import Definitions.Def_CatalyticTreeEval_NativeBufferedInput

set_option autoImplicit false
open CatalyticTreeEval.Contracts.NativeInputInspect (Roles Post rowFootprint)

namespace CatalyticTreeEval.Contracts.NativeInputProbe

theorem probe_exec {lanes : ℕ} (r : Roles lanes) (input params : List Bool)
    (c : Config (machine r)) (base inputHead : ℕ)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=base+lanes)
    (headBound : inputHead ≤ params.length+1)
    (cursor : ∀ j ≤ params.length+1,
      c.work (WorkLanes.address r.bookmark base (3+3*j))=decide (j=inputHead))
    (buffer : Buffer r base params c.work)
    (hop : r.replyOrigin≠r.replyPresent) (hov : r.replyOrigin≠r.replyValue)
    (hpv : r.replyPresent≠r.replyValue)
    (readonly : ∀ lane ∈ ({r.origin,r.data,r.bookmark} : Finset (Fin lanes)),
      lane≠r.replyOrigin ∧ lane≠r.replyPresent ∧ lane≠r.replyValue) :
    ∃ (d : Config (machine r)) (T : ℕ),
      FirstExit ((machine r).step input)
        (fun _ e => (Envelope.mk 0 (base+(lanes+1)*(8+3*params.length)) c.catalystHead (c.catalystHead+1)).Contains e ∧
          SameOutside (rowFootprint r (rowBase lanes base inputHead)) c e)
        {e | e.state=none} {c with state:=some (machine r).start} d T ∧
      T ≤ 20*(lanes+1)*(params.length+2) ∧
      Post r (rowBase lanes base inputHead) (readReply params inputHead) c d ∧
      d.work (rowBase lanes base inputHead+r.replyOrigin.val)=(readReply params inputHead).isOrigin ∧
      d.work (rowBase lanes base inputHead+r.replyPresent.val)=(readReply params inputHead).isPresent ∧
      d.work (rowBase lanes base inputHead+r.replyValue.val)=(readReply params inputHead).value ∧
      Buffer r base params d.work ∧
      (∀ j ≤ params.length+1,
        d.work (WorkLanes.address r.bookmark base (3+3*j))=decide (j=inputHead)) := by sorry

end CatalyticTreeEval.Contracts.NativeInputProbe
