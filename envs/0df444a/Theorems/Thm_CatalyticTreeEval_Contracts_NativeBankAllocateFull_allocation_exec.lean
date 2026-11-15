-- Prove2me | Theorems.Thm_CatalyticTreeEval_Contracts_NativeBankAllocateFull_allocation_exec
-- name    : CatalyticTreeEval.Contracts.NativeBankAllocateFull.allocation_exec
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-14T10:25:54.540461+00:00
-- url     : https://prove2.me/theorems/d061fe03-74bb-4942-8b59-35b66d006761
-- title:
--   Charged native allocation of tagged binary operand banks
-- statement:
--   Fix counter and bookmark lanes and a finite set of operand lanes. From an actual binary counter of value N and blank bookmark/operand lanes, one fixed finite native machine initializes N tagged zero columns in every operand lane, consumes counter A while preserving counter B, erases its temporary bookmark and returns to the counter flag. Every native prefix stays inside the physical work bound base+(K+1)(7+3 max(N,counterWidth)), preserves the caller prefix and all catalyst data, and keeps the catalyst head at its initial position. If N and counterWidth are at most W, the whole operation, including bookmark seeding and erasure, takes at most 200(K+1)(W+1)^2+1 native transitions. No width, address or allocation count occurs in the transition table. Counter preparation is an explicit precondition and remains a separately charged caller obligation.
-- source:
--   Shared native-machine initialization for Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3. Supports computed-bank arithmetic, decoder and evaluator workspace contracts.

import Definitions.Def_CatalyticTreeEval_NativeBankAllocation

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.NativeBankAllocateFull

theorem allocation_exec {lanes : ℕ} (counter bookmark : Fin lanes)
    (selected : Finset (Fin lanes)) (notSelected : bookmark ∉ selected)
    (notCounter : counter ∉ selected) (distinct : counter ≠ bookmark)
    (input : List Bool) (c : Config (machine counter bookmark selected))
    (base counterWidth width : ℕ) (a b : ℕ → Bool)
    (hi : c.inputHead ≤ input.length+1) (hc : c.catalystHead ≤ c.catalyst.length)
    (head : c.workHead=WorkLanes.address counter base 0)
    (origin : WorkLanes.OriginTrack lanes base c.work)
    (blankBook : ∀ p, c.work (WorkLanes.address bookmark base p)=false)
    (blankSelected : ∀ lane ∈ selected, ∀ p, c.work (WorkLanes.address lane base p)=false)
    (marker : c.work (WorkLanes.address counter base 3)=false)
    (flag : c.work (WorkLanes.address counter base 0)=decide (0<BinaryCountdown.bankValue a counterWidth))
    (bank : ShiftAppend.bankContents (fun p => c.work (WorkLanes.address counter base p)) 6 counterWidth a b)
    (counterFits : counterWidth ≤ width) (countFits : BinaryCountdown.bankValue a counterWidth ≤ width) :
    ∃ (d : Config (machine counter bookmark selected)) (T : ℕ),
      FirstExit ((machine counter bookmark selected).step input)
        (fun _ e => (Envelope.mk 0 (base+(lanes+1)*(7+3*max (BinaryCountdown.bankValue a counterWidth) counterWidth))
          c.catalystHead (c.catalystHead+1)).Contains e ∧
          SameOutside ⟨Set.Ico base (base+(lanes+1)*(7+3*max (BinaryCountdown.bankValue a counterWidth) counterWidth)),∅⟩ c e)
        {e | e.state=none} {c with state:=some (machine counter bookmark selected).start} d T ∧
      T ≤ 200*(lanes+1)*(width+1)^2+1 ∧
      d.workHead=WorkLanes.address counter base 0 ∧ WorkLanes.OriginTrack lanes base d.work ∧
      (∀ p, d.work (WorkLanes.address bookmark base p)=false) ∧
      ShiftAppend.bankContents (fun p => d.work (WorkLanes.address counter base p)) 6 counterWidth
        (BinarySeek.digitsAt a (BinaryCountdown.bankValue a counterWidth)) b ∧
      BinaryCountdown.bankValue (BinarySeek.digitsAt a (BinaryCountdown.bankValue a counterWidth)) counterWidth=0 ∧
      d.work (WorkLanes.address counter base 0)=false ∧
      d.work (WorkLanes.address counter base 3)=false ∧
      (∀ lane ∈ selected, ShiftAppend.bankContents (fun p => d.work (WorkLanes.address lane base p))
        6 (BinaryCountdown.bankValue a counterWidth) (fun _ => false) (fun _ => false)) ∧
      (∀ lane ∈ selected, ∀ p < 6, d.work (WorkLanes.address lane base p)=false) ∧
      SavedPrefix base c d ∧ d.catalyst=c.catalyst ∧ d.output=c.output := by
  sorry

end CatalyticTreeEval.Contracts.NativeBankAllocateFull
