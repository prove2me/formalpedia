-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_9
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:20:51.115649+00:00
-- url     : https://prove2.me/theorems/42391dc3-563f-415d-b20c-055f37d7839a
-- title:
--   Pointer readout and public initialization
-- statement:
--   Let a source program be a fixed finite deterministic scalar RAM program. Host states contain natural and real registers and memory; scaled instances, cached observations, advancing pointers and dirty queues are the objects defined by the wrapper interface.
--
--   Native pointer reads and selected-scale reads return the cache value designated by the mathematical advancing pointer. Public initialization builds the answer table, marks and commits the required vertices, and establishes the initialized wrapper memory image. Query and commit frames preserve source banks and unrelated public entries.
--
--   For every parameter tuple and state satisfying the explicit source-execution and representation hypotheses, all component contracts hold simultaneously:
--
--   $$
--   \bigwedge_{j\in J} L_j.
--   $$
--
--   Here the component assertions $L_j$ are the execution, exact memory-image, preservation, observation and charged-cost contracts described above, each with its own universal quantifiers. They are used to verify the arbitrary-weight scaling reduction for $n\ge2$ and $1/m<\epsilon\le1$.
--
--   **Formalization Note** The collection uses a balanced conjunction so its component contracts can be reused through short projections. It does not supply correctness or termination as a hypothesis on the external graph input.
-- source:
--   Cui, Li, Miao and Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, October 2026 submission #912, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf, p.4 unnumbered arbitrary-weight scaling reduction, with delta_L=epsilon L/(128n), internal accuracy epsilon/16 and size padding64m; p.18 scalar unit-cost arithmetic model. Component contracts verify the explicit finite native wrapper in DecrAlmostLinearSSSP_RAMFoundation.

import Definitions.Def_DecrAlmostLinearSSSP_RAMFoundation
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable

theorem DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_9 : (((((((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.Native.pointerStart) ∧ (DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.Native.pointerStart)) ∧ ((∀ {record pointer flags list cost : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.pointerStart s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list t) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat}
  {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PointerPrefix i B reserve N b i.n s →
    @DecrAlmostLinearSSSP.Decremental.DirtyMark.View i.n
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
          reserve N).flags
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
          reserve N).list
      (List.finRange i.n) s))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B reserve N : Nat)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Native.Globals i B
      (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
          N).utility
      s →
    DecrAlmostLinearSSSP.Decremental.Native.PointerBases
        (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
            reserve N).record
        (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
            reserve N).pointer
        (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
            reserve N).flags
        (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
            reserve N).list
        s →
      DecrAlmostLinearSSSP.Decremental.Native.ScanTable i
          (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
              reserve N).record
          (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
              reserve N).cache
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N)
            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          b s →
        ∃ cost t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.buildPointers s
              cost t)
            (And
              (@LE.le.{0} Nat instLENat cost
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                        (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                      (@OfNat.ofNat.{0} Nat (nat_lit 28) (instOfNatNat (nat_lit 28))))
                    i.n)
                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
              (And (DecrAlmostLinearSSSP.Decremental.Native.PointerPrefix i B reserve N b i.n t)
                (DecrAlmostLinearSSSP.Decremental.Native.PublicFrame
                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N)
                  i.n s t)))) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.Native.pointerStart)) ∧ ((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.Native.buildPointers) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ cost t,
      And (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.PointerRead.code s cost t)
        (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (And
            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
              (@ite.{1} Nat
                (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (instDecidableEqNat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (s.natMem (DecrAlmostLinearSSSP.Decremental.PointerRead.cellAddress s))))
            (And
              (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
                (@ite.{1} Real
                  (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (instDecidableEqNat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (s.realMem (DecrAlmostLinearSSSP.Decremental.PointerRead.cellAddress s))))
              (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem)))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ cost t,
      And (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.PointerRead.code s cost t)
        (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (And
            (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.ExtendedMax.incoming t)
              (@ite.{1} ENNReal
                (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (instDecidableEqNat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@Top.top.{0} ENNReal ENNReal.instTop)
                (DecrAlmostLinearSSSP.Decremental.ExtendedMax.cell s
                  (DecrAlmostLinearSSSP.Decremental.PointerRead.cellAddress s))))
            (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem))))))))) ∧ ((((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.PointerRead.code) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.SelectedRead.prefixCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.SelectedRead.prefixData s))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.SelectedRead.prefixData s).natReg
        (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))))
    (And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.SelectedRead.prefixData s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94)))))))
      (∀ (k : Nat),
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
            @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.SelectedRead.prefixData s).natReg k) (s.natReg k)))) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.SelectedRead.code))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ cost t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.SelectedRead.chooseCode s
          cost t)
        (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))))
          (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.ExtendedMax.incoming t)
            (@ite.{1} ENNReal
              (@Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
              (instDecidableEqNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
              (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))
              (@ite.{1} ENNReal
                (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (instDecidableEqNat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@Top.top.{0} ENNReal ENNReal.instTop)
                (DecrAlmostLinearSSSP.Decremental.ExtendedMax.cell s
                  (DecrAlmostLinearSSSP.Decremental.PointerRead.cellAddress s))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ cost t,
      And (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.SelectedRead.code s cost t)
        (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
          (And
            (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.ExtendedMax.incoming t)
              (DecrAlmostLinearSSSP.Decremental.SelectedRead.value s))
            (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem)))))) ∧ ((∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.SelectedRead.chooseCode s cost t →
      And
        (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
          (@ite.{1} Nat
            (@Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
            (instDecidableEqNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (@ite.{1} Nat
              (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (instDecidableEqNat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (s.natMem (DecrAlmostLinearSSSP.Decremental.PointerRead.cellAddress s)))))
        (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
          (@ite.{1} Real
            (@Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
            (instDecidableEqNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@ite.{1} Real
              (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (instDecidableEqNat (DecrAlmostLinearSSSP.Decremental.PointerRead.pointer s)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (s.realMem (DecrAlmostLinearSSSP.Decremental.PointerRead.cellAddress s)))))) ∧ ((∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.SelectedRead.code s cost t →
      And
        (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
          (DecrAlmostLinearSSSP.Decremental.SelectedRead.flag s))
        (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
          (DecrAlmostLinearSSSP.Decremental.SelectedRead.realValue s))) ∧ (∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.SelectedRead.code s cost t →
      @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.SelectedRead.flag s)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.SelectedRead.flag s)
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (DecrAlmostLinearSSSP.Decremental.SelectedRead.realValue s)) →
          And
            (@LE.le.{0} Nat instLENat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))))))))) ∧ (((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.SelectedRead.code k) ∧ (∀ {n : Nat} {l : DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout n}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l s →
    (∀ (address : Nat),
        @DecrAlmostLinearSSSP.Decremental.AnswerTable.Protected n l address →
          And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
            (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
      @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l t)) ∧ ((∀ {n : Nat} (l : DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout n)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (v : Fin n),
  @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
        (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.pointerBase n l) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
          (@Fin.val n (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.source n l)) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94)))) (@Fin.val n v) →
          And
            (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.SelectedRead.flag s)
              (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag n l v))
            (@Eq.{1} Real (DecrAlmostLinearSSSP.Decremental.SelectedRead.realValue s)
              (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.realValue n l v))) ∧ (∀ {n : Nat} {l : DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout n}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l s →
    @Eq.{1} (Nat → Nat) t.natMem s.natMem →
      @Eq.{1} (Nat → Real) t.realMem s.realMem → @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l t))) ∧ (((∀ {n : Nat} (l : DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout n),
  (∀ (v : Fin n),
      @LE.le.{0} Nat instLENat (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.cacheFlag n l v)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
    (∀ (v : Fin n),
        @Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.cacheFlag n l v)
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.cacheReal n l v)) →
      ∀ (v : Fin n),
        And
          (@LE.le.{0} Nat instLENat (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag n l v)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag n l v)
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.realValue n l v))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {base stride j : Nat},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) base →
    Iff
      (@Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.Native.scanRecord i base stride j)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.scaleCount i)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (recordBase cacheBase stride pointerBase : Nat) (p : Fin i.n → Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
  DecrAlmostLinearSSSP.Decremental.Native.ScanTable i recordBase cacheBase stride b s →
    (∀ (v : Fin i.n),
        @Eq.{1} Nat
          (s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pointerBase
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
          (DecrAlmostLinearSSSP.Decremental.Native.scanRecord i recordBase stride (p v))) →
      @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image i.n
        (DecrAlmostLinearSSSP.Decremental.Native.answerLayout i recordBase cacheBase stride pointerBase p s) s) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (recordBase cacheBase stride pointerBase : Nat) (p : Fin i.n → Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
  DecrAlmostLinearSSSP.Decremental.Native.ScanTable i recordBase cacheBase stride b s →
    ∀ (v : Fin i.n),
      And
        (@LE.le.{0} Nat instLENat
          (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag i.n
            (DecrAlmostLinearSSSP.Decremental.Native.answerLayout i recordBase cacheBase stride pointerBase p s) v)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Eq.{1} Nat
            (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag i.n
              (DecrAlmostLinearSSSP.Decremental.Native.answerLayout i recordBase cacheBase stride pointerBase p s) v)
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.realValue i.n
              (DecrAlmostLinearSSSP.Decremental.Native.answerLayout i recordBase cacheBase stride pointerBase p s) v))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (recordBase cacheBase stride pointerBase : Nat) (p : Fin i.n → Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
  DecrAlmostLinearSSSP.Decremental.Native.ScanTable i recordBase cacheBase stride b s →
    ∀ (v : Fin i.n),
      @Eq.{1} ENNReal
        (@ite.{1} ENNReal
          (@Eq.{1} Nat
            (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag i.n
              (DecrAlmostLinearSSSP.Decremental.Native.answerLayout i recordBase cacheBase stride pointerBase p s) v)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (instDecidableEqNat
            (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag i.n
              (DecrAlmostLinearSSSP.Decremental.Native.answerLayout i recordBase cacheBase stride pointerBase p s) v)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Top.top.{0} ENNReal ENNReal.instTop)
          (ENNReal.ofReal
            (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.realValue i.n
              (DecrAlmostLinearSSSP.Decremental.Native.answerLayout i recordBase cacheBase stride pointerBase p s) v)))
        (DecrAlmostLinearSSSP.Decremental.selected i b p v)))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B reserve N : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (p : Fin i.n → Nat),
  DecrAlmostLinearSSSP.Decremental.Native.ScanTable i
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
          reserve N).record
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
          reserve N).cache
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N)
        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
      b s →
    @LE.le.{0} Nat instLENat i.n B →
      ∀ (address : Nat),
        @DecrAlmostLinearSSSP.Decremental.AnswerTable.Protected i.n
            (DecrAlmostLinearSSSP.Decremental.Native.answerLayout i
              (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                  (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).record
              (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                  (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).cache
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N)
                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
              (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                  (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).pointer
              p s)
            address →
          And (@LE.le.{0} Nat instLENat i.n address)
            (∀ (v : Fin i.n),
              @Ne.{1} Nat address
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).flags
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyCommit.suffix s
    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
    (DecrAlmostLinearSSSP.Decremental.DirtyCommit.afterStores s))) ∧ ((∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.SelectedRead.code s cost t →
    ∀ (k : Nat),
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
                  @Eq.{1} Nat (t.natReg k) (s.natReg k)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        @Ne.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192)))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))))) →
          ∃ cost t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyCommit.body s cost
                t)
              (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))
                (And
                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (And
                    (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 194) (instOfNatNat (nat_lit 194))))
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 194) (instOfNatNat (nat_lit 194))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (And
                      (@Eq.{1} Nat
                        (t.natMem
                          (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))))
                        (DecrAlmostLinearSSSP.Decremental.SelectedRead.flag
                          (DecrAlmostLinearSSSP.Decremental.DirtyCommit.loaded s)))
                      (And
                        (@Eq.{1} Real
                          (t.realMem
                            (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))))
                          (DecrAlmostLinearSSSP.Decremental.SelectedRead.realValue
                            (DecrAlmostLinearSSSP.Decremental.DirtyCommit.loaded s)))
                        (And
                          (@Eq.{1} Nat
                            (t.natMem
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                  (s.natMem
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (∀ (address : Nat),
                            @Ne.{1} Nat address
                                (s.natMem
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))) →
                              @Ne.{1} Nat address
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                      (s.natMem
                                        (s.natReg
                                          (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))))) →
                                And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                  (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 184) (instOfNatNat (nat_lit 184))) →
                  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))) →
                    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 194) (instOfNatNat (nat_lit 194))) →
                      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                        DecrAlmostLinearSSSP.Decremental.DirtyCommit.body k)))) ∧ (((∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyCommit.body s cost t →
    And
      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))
      (And
        (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))))
        (And
          (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))))
          (And
            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
            (And
              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96)))))
              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98)))))))))) ∧ (∀ {n : Nat} (l : DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout n) (flagBase listBase : Nat),
  @LE.le.{0} Nat instLENat n flagBase →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flagBase
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
        listBase →
      (∀ (address : Nat),
          @DecrAlmostLinearSSSP.Decremental.AnswerTable.Protected n l address →
            And (@LE.le.{0} Nat instLENat n address)
              (∀ (v : Fin n),
                @Ne.{1} Nat address
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flagBase
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n v))))) →
        ∀ (xs : List.{0} (Fin n)) (readBase : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          @LE.le.{0} Nat instLENat listBase readBase →
            @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l s →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
                  (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.pointerBase n l) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                    (@Fin.val n (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.source n l)) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98)))) flagBase →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))
                              readBase →
                            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 194) (instOfNatNat (nat_lit 194))))
                                (@List.length.{0} (Fin n) xs) →
                              (∀ (j : Nat) (hj : @LT.lt.{0} Nat instLTNat j (@List.length.{0} (Fin n) xs)),
                                  @Eq.{1} Nat
                                    (s.natMem
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) readBase
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                                    (@Fin.val n
                                      (@GetElem.getElem.{0, 0, 0} (List.{0} (Fin n)) Nat (Fin n)
                                        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} (Fin n) as))
                                        (@List.instGetElemNatLtLength.{0} (Fin n)) xs j hj))) →
                                ∃ cost t,
                                  And
                                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                      DecrAlmostLinearSSSP.Decremental.DirtyCommit.loop s cost t)
                                    (And
                                      (@LE.le.{0} Nat instLENat cost
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))
                                            (@List.length.{0} (Fin n) xs))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                      (And
                                        (@Eq.{1} Nat
                                          (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) readBase
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              (@List.length.{0} (Fin n) xs))))
                                        (And
                                          (@Eq.{1} Nat
                                            (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 194) (instOfNatNat (nat_lit 194))))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                          (And (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l t)
                                            (And
                                              (∀ (v : Fin n),
                                                @Membership.mem.{0, 0} (Fin n) (List.{0} (Fin n))
                                                    (@List.instMembership.{0} (Fin n)) xs v →
                                                  And
                                                    (@Eq.{1} Nat (t.natMem (@Fin.val n v))
                                                      (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag n l v))
                                                    (And
                                                      (@Eq.{1} Real (t.realMem (@Fin.val n v))
                                                        (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.realValue
                                                          n l v))
                                                      (@Eq.{1} Nat
                                                        (t.natMem
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) flagBase
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              (@Fin.val n v))))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                                              (∀ (address : Nat),
                                                (∀ (v : Fin n),
                                                    @Membership.mem.{0, 0} (Fin n) (List.{0} (Fin n))
                                                        (@List.instMembership.{0} (Fin n)) xs v →
                                                      And (@Ne.{1} Nat address (@Fin.val n v))
                                                        (@Ne.{1} Nat address
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) flagBase
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              (@Fin.val n v))))) →
                                                  And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                    (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyCommit.beginCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.DirtyCommit.beginData s)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyCommit.endCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.DirtyCommit.endData s)) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 184) (instOfNatNat (nat_lit 184))) →
                  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))) →
                    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 194) (instOfNatNat (nat_lit 194))) →
                      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                        DecrAlmostLinearSSSP.Decremental.DirtyCommit.loop k))))))) ∧ ((((((∀ {n : Nat} (l : DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout n) (flagBase listBase : Nat),
  @LE.le.{0} Nat instLENat n flagBase →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flagBase
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n))
        listBase →
      (∀ (address : Nat),
          @DecrAlmostLinearSSSP.Decremental.AnswerTable.Protected n l address →
            And (@LE.le.{0} Nat instLENat n address)
              (∀ (v : Fin n),
                @Ne.{1} Nat address
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flagBase
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n v))))) →
        ∀ (xs : List.{0} (Fin n)) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          @DecrAlmostLinearSSSP.Decremental.DirtyMark.View n flagBase listBase xs s →
            @DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l s →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
                  (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.pointerBase n l) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                    (@Fin.val n (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.source n l)) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98)))) flagBase →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 102) (instOfNatNat (nat_lit 102)))) listBase →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                            (∀ v ∉ xs,
                                And
                                  (@Eq.{1} Nat (s.natMem (@Fin.val n v))
                                    (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag n l v))
                                  (@Eq.{1} Real (s.realMem (@Fin.val n v))
                                    (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.realValue n l v))) →
                              ∃ cost t,
                                And
                                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                    DecrAlmostLinearSSSP.Decremental.DirtyCommit.code s cost t)
                                  (And
                                    (@LE.le.{0} Nat instLENat cost
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))
                                          (@List.length.{0} (Fin n) xs))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                                    (And
                                      (@DecrAlmostLinearSSSP.Decremental.DirtyMark.View n flagBase listBase
                                        (@List.nil.{0} (Fin n)) t)
                                      (And (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Image n l t)
                                        (And
                                          (∀ (v : Fin n),
                                            And
                                              (@Eq.{1} Nat (t.natMem (@Fin.val n v))
                                                (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.flag n l v))
                                              (@Eq.{1} Real (t.realMem (@Fin.val n v))
                                                (@DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout.realValue n l v)))
                                          (∀ (address : Nat),
                                            (∀ (v : Fin n),
                                                @Membership.mem.{0, 0} (Fin n) (List.{0} (Fin n))
                                                    (@List.instMembership.{0} (Fin n)) xs v →
                                                  And (@Ne.{1} Nat address (@Fin.val n v))
                                                    (@Ne.{1} Nat address
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        flagBase
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          (@Fin.val n v))))) →
                                              And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.SelectedRead.code k)) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 184) (instOfNatNat (nat_lit 184))) →
                  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 192) (instOfNatNat (nat_lit 192))) →
                    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 194) (instOfNatNat (nat_lit 194))) →
                      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))) →
                        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))) →
                          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                            DecrAlmostLinearSSSP.Decremental.DirtyCommit.code k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.DirtyCommit.code k))) ∧ (((DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.DirtyCommit.code) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.DirtyCommit.code)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B reserve N : Nat)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Native.PointerPrefix i B reserve N b i.n s →
    @LE.le.{0} Nat instLENat i.n B →
      ∃ cost t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyCommit.code s cost t)
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) i.n)
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
            (And
              (DecrAlmostLinearSSSP.Decremental.Native.Globals i B
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).utility
                t)
              (And
                (@DecrAlmostLinearSSSP.Decremental.DirtyMark.View i.n
                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).flags
                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).list
                  (@List.nil.{0} (Fin i.n)) t)
                (And
                  (∀ (v : Fin i.n),
                    And
                      (@LE.le.{0} Nat instLENat (t.natMem (@Fin.val i.n v))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (@Eq.{1} Nat (t.natMem (@Fin.val i.n v))
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                        @LE.le.{0} Real Real.instLE
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                          (t.realMem (@Fin.val i.n v))))
                  (And
                    (∀ (v : Fin i.n),
                      @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored t.machine (@Fin.val i.n v))
                        (DecrAlmostLinearSSSP.Decremental.selected i b
                          (DecrAlmostLinearSSSP.Decremental.Native.initialPointers i b) v))
                    (And
                      (∀ (v : Fin i.n),
                        @Eq.{1} Nat
                          (t.natMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                  (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).pointer
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
                          (DecrAlmostLinearSSSP.Decremental.Native.scanRecord i
                            (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).record
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N)
                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                            (DecrAlmostLinearSSSP.Decremental.Native.initialPointers i b v)))
                      (DecrAlmostLinearSSSP.Decremental.Native.PublicFrame
                        (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                          (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N)
                        i.n s t)))))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (es : List.{0} (Fin i.k)),
      (∀ (e : Fin i.k),
          @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k)) es e →
            @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (DecrAlmostLinearSSSP.Decremental.scale j))) →
        And
          (@LE.le.{0} Real Real.instLE
            (@List.sum.{0} Real Real.instAdd Real.instZero
              (@List.map.{0, 0} (Fin i.k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (i.weight e)) es))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (DecrAlmostLinearSSSP.Decremental.delta i j)
              (@List.sum.{0} Real Real.instAdd Real.instZero
                (@List.map.{0, 0} (Fin i.k) Real
                  (fun e => @Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.barrierWeight i j e))
                  es))))
          (@LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (DecrAlmostLinearSSSP.Decremental.delta i j)
              (@List.sum.{0} Real Real.instAdd Real.instZero
                (@List.map.{0, 0} (Fin i.k) Real
                  (fun e => @Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.barrierWeight i j e))
                  es)))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@List.sum.{0} Real Real.instAdd Real.instZero
                (@List.map.{0, 0} (Fin i.k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (i.weight e)) es))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast (@List.length.{0} (Fin i.k) es))
                (DecrAlmostLinearSSSP.Decremental.delta i j))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (active : Finset.{0} (Fin i.k)) {u v : Fin i.n} {es : List.{0} (Fin i.k)},
      @DecrAlmostLinearSSSP.Decremental.Walk i.n i.k i.graph active u v es →
        (∀ (e : Fin i.k),
            @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k)) es e →
              @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (DecrAlmostLinearSSSP.Decremental.scale j))) →
          @LE.le.{0} ENNReal ENNReal.instLE
            (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
              (@instHMul.{0} ENNReal
                (@Distrib.toMul.{0} ENNReal
                  (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
              (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j))
              (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.barrierInput i j).n
                (DecrAlmostLinearSSSP.Decremental.barrierInput i j).k
                (DecrAlmostLinearSSSP.Decremental.barrierInput i j).graph active
                (fun e =>
                  @Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    ((DecrAlmostLinearSSSP.Decremental.barrierInput i j).weight e))
                u v))
            (ENNReal.ofReal
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@List.sum.{0} Real Real.instAdd Real.instZero
                  (@List.map.{0, 0} (Fin i.k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (i.weight e)) es))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast (@List.length.{0} (Fin i.k) es))
                  (DecrAlmostLinearSSSP.Decremental.delta i j))))))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (active : Finset.{0} (Fin i.k)) (u v : Fin i.n),
      @LE.le.{0} ENNReal ENNReal.instLE
          (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
            (@instHMul.{0} ENNReal
              (@Distrib.toMul.{0} ENNReal
                (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
            (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j))
            (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.barrierInput i j).n
              (DecrAlmostLinearSSSP.Decremental.barrierInput i j).k
              (DecrAlmostLinearSSSP.Decremental.barrierInput i j).graph active
              (fun e =>
                @Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  ((DecrAlmostLinearSSSP.Decremental.barrierInput i j).weight e))
              u v))
          (ENNReal.ofReal
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (DecrAlmostLinearSSSP.Decremental.scale j))) →
        @LE.le.{0} ENNReal ENNReal.instLE
          (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
            (fun e =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                (i.weight e))
            u v)
          (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
            (@instHMul.{0} ENNReal
              (@Distrib.toMul.{0} ENNReal
                (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
            (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j))
            (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.barrierInput i j).n
              (DecrAlmostLinearSSSP.Decremental.barrierInput i j).k
              (DecrAlmostLinearSSSP.Decremental.barrierInput i j).graph active
              (fun e =>
                @Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  ((DecrAlmostLinearSSSP.Decremental.barrierInput i j).weight e))
              u v))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (j : Nat),
  @Eq.{1} Real
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Nat.cast.{0} Real Real.instNatCast i.n)
      (DecrAlmostLinearSSSP.Decremental.delta i j))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) i.accuracy
        (DecrAlmostLinearSSSP.Decremental.scale j))
      (@OfNat.ofNat.{0} Real (nat_lit 128)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126)))))))))) ∧ ((∀ {epsilon d L : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) epsilon →
    @LE.le.{0} Real Real.instLE epsilon (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) d →
        @LE.le.{0} Real Real.instLE L
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              d) →
          @LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) epsilon
                  (@OfNat.ofNat.{0} Real (nat_lit 16)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) d
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) epsilon L)
                  (@OfNat.ofNat.{0} Real (nat_lit 128)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126))))))))))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) epsilon
                  (@OfNat.ofNat.{0} Real (nat_lit 8)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
              d)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (active : Finset.{0} (Fin i.k)) (u v : Fin i.n) (B : ENNReal),
      @DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph active u v →
        @LE.le.{0} ENNReal ENNReal.instLE
            (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
              (fun e =>
                @Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  (i.weight e))
              u v)
            (ENNReal.ofReal
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (DecrAlmostLinearSSSP.Decremental.scale j))) →
          @LE.le.{0} ENNReal ENNReal.instLE B
              (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                (@instHMul.{0} ENNReal
                  (@Distrib.toMul.{0} ENNReal
                    (@instDistribOfSemiring.{0} ENNReal
                      (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                (ENNReal.ofReal
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                      (@OfNat.ofNat.{0} Real (nat_lit 16)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
                (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
                  (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k
                  (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph
                  (DecrAlmostLinearSSSP.Decremental.scaleActive i j active)
                  (fun e =>
                    @Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
                  u v)) →
            ∃ d,
              And
                (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  d)
                (And
                  (@Eq.{1} ENNReal
                    (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
                      (fun e =>
                        @Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (i.weight e))
                      u v)
                    (ENNReal.ofReal d))
                  (@LE.le.{0} ENNReal ENNReal.instLE
                    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                      (@instHMul.{0} ENNReal
                        (@Distrib.toMul.{0} ENNReal
                          (@instDistribOfSemiring.{0} ENNReal
                            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                      (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j)) B)
                    (ENNReal.ofReal
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 16)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) d
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) i.accuracy
                              (DecrAlmostLinearSSSP.Decremental.scale j))
                            (@OfNat.ofNat.{0} Real (nat_lit 128)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126)))))))))))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (active : Finset.{0} (Fin i.k)) (u v : Fin i.n) (B : ENNReal) (d : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) d →
        @Eq.{1} ENNReal
            (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
              (fun e =>
                @Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  (i.weight e))
              u v)
            (ENNReal.ofReal d) →
          @DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph active u v →
            @LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.scale j)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  d) →
              @LE.le.{0} ENNReal ENNReal.instLE
                  (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
                    (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k
                    (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph
                    (DecrAlmostLinearSSSP.Decremental.scaleActive i j active)
                    (fun e =>
                      @Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
                    u v)
                  B →
                @LE.le.{0} ENNReal ENNReal.instLE B
                    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                      (@instHMul.{0} ENNReal
                        (@Distrib.toMul.{0} ENNReal
                          (@instDistribOfSemiring.{0} ENNReal
                            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                      (ENNReal.ofReal
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 16)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
                      (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
                        (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k
                        (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph
                        (DecrAlmostLinearSSSP.Decremental.scaleActive i j active)
                        (fun e =>
                          @Nat.cast.{0} ENNReal
                            (@AddMonoidWithOne.toNatCast.{0} ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                            ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
                        u v)) →
                  @LE.le.{0} ENNReal ENNReal.instLE
                      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                        (@instHMul.{0} ENNReal
                          (@Distrib.toMul.{0} ENNReal
                            (@instDistribOfSemiring.{0} ENNReal
                              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                        (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j)) B)
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (DecrAlmostLinearSSSP.Decremental.scale j))) →
                    And
                      (@LE.le.{0} ENNReal ENNReal.instLE (ENNReal.ofReal d)
                        (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                          (@instHMul.{0} ENNReal
                            (@Distrib.toMul.{0} ENNReal
                              (@instDistribOfSemiring.{0} ENNReal
                                (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                          (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j)) B))
                      (@LE.le.{0} ENNReal ENNReal.instLE
                        (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                          (@instHMul.{0} ENNReal
                            (@Distrib.toMul.{0} ENNReal
                              (@instDistribOfSemiring.{0} ENNReal
                                (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                          (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j)) B)
                        (ENNReal.ofReal
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                                (@OfNat.ofNat.{0} Real (nat_lit 8)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
                            d))))))) ∧ (((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {a b : Finset.{0} (Fin k)},
  @LE.le.{0} (Finset.{0} (Fin k))
      (@Preorder.toLE.{0} (Finset.{0} (Fin k))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin k)) (@Finset.instPartialOrder.{0} (Fin k))))
      a b →
    ∀ {u v : Fin n} {es : List.{0} (Fin k)},
      @DecrAlmostLinearSSSP.Decremental.Walk n k g a u v es → @DecrAlmostLinearSSSP.Decremental.Walk n k g b u v es) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) {a b : Finset.{0} (Fin k)},
  @LE.le.{0} (Finset.{0} (Fin k))
      (@Preorder.toLE.{0} (Finset.{0} (Fin k))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin k)) (@Finset.instPartialOrder.{0} (Fin k))))
      a b →
    ∀ (w : Fin k → ENNReal) (u v : Fin n),
      @LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.distance n k g b w u v)
        (@DecrAlmostLinearSSSP.Decremental.distance n k g a w u v))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (current past : Finset.{0} (Fin i.k)),
      @LE.le.{0} (Finset.{0} (Fin i.k))
          (@Preorder.toLE.{0} (Finset.{0} (Fin i.k))
            (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin i.k)) (@Finset.instPartialOrder.{0} (Fin i.k))))
          current past →
        ∀ {u v : Fin i.n} {es : List.{0} (Fin i.k)},
          @DecrAlmostLinearSSSP.Decremental.Walk i.n i.k i.graph current u v es →
            (∀ (e : Fin i.k),
                @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k)) es e →
                  @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      (DecrAlmostLinearSSSP.Decremental.scale j))) →
              ∀ (B : ENNReal),
                @LE.le.{0} ENNReal ENNReal.instLE B
                    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                      (@instHMul.{0} ENNReal
                        (@Distrib.toMul.{0} ENNReal
                          (@instDistribOfSemiring.{0} ENNReal
                            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                      (ENNReal.ofReal
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 16)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
                      (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
                        (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k
                        (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph
                        (DecrAlmostLinearSSSP.Decremental.scaleActive i j past)
                        (fun e =>
                          @Nat.cast.{0} ENNReal
                            (@AddMonoidWithOne.toNatCast.{0} ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                            ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
                        u v)) →
                  @LE.le.{0} ENNReal ENNReal.instLE
                    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                      (@instHMul.{0} ENNReal
                        (@Distrib.toMul.{0} ENNReal
                          (@instDistribOfSemiring.{0} ENNReal
                            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                      (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j)) B)
                    (ENNReal.ofReal
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 16)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@List.sum.{0} Real Real.instAdd Real.instZero
                            (@List.map.{0, 0} (Fin i.k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (i.weight e))
                              es))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@Nat.cast.{0} Real Real.instNatCast (@List.length.{0} (Fin i.k) es))
                            (DecrAlmostLinearSSSP.Decremental.delta i j)))))) ∧ ((∀ (delta x y bound : ENNReal),
  @LE.le.{0} ENNReal ENNReal.instLE
      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
        (@instHMul.{0} ENNReal
          (@Distrib.toMul.{0} ENNReal
            (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
        delta x)
      bound →
    @LE.le.{0} ENNReal ENNReal.instLE
        (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
          (@instHMul.{0} ENNReal
            (@Distrib.toMul.{0} ENNReal
              (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
          delta y)
        bound →
      @LE.le.{0} ENNReal ENNReal.instLE
        (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
          (@instHMul.{0} ENNReal
            (@Distrib.toMul.{0} ENNReal
              (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
          delta (@Max.max.{0} ENNReal ENNReal.instMax x y))
        bound) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) {ι : Type} (S : Finset.{0} ι) (past : ι → Finset.{0} (Fin i.k)) (current : Finset.{0} (Fin i.k)),
      (∀ (t : ι),
          @Membership.mem.{0, 0} ι (Finset.{0} ι)
              (@SetLike.instMembership.{0, 0} (Finset.{0} ι) ι (@Finset.instSetLike.{0} ι)) S t →
            @LE.le.{0} (Finset.{0} (Fin i.k))
              (@Preorder.toLE.{0} (Finset.{0} (Fin i.k))
                (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin i.k)) (@Finset.instPartialOrder.{0} (Fin i.k))))
              current (past t)) →
        ∀ {u v : Fin i.n} {es : List.{0} (Fin i.k)},
          @DecrAlmostLinearSSSP.Decremental.Walk i.n i.k i.graph current u v es →
            (∀ (e : Fin i.k),
                @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k)) es e →
                  @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      (DecrAlmostLinearSSSP.Decremental.scale j))) →
              ∀ (B : ι → ENNReal),
                (∀ (t : ι),
                    @Membership.mem.{0, 0} ι (Finset.{0} ι)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} ι) ι (@Finset.instSetLike.{0} ι)) S t →
                      @LE.le.{0} ENNReal ENNReal.instLE (B t)
                        (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                          (@instHMul.{0} ENNReal
                            (@Distrib.toMul.{0} ENNReal
                              (@instDistribOfSemiring.{0} ENNReal
                                (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                          (ENNReal.ofReal
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                                (@OfNat.ofNat.{0} Real (nat_lit 16)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
                          (@DecrAlmostLinearSSSP.Decremental.distance
                            (DecrAlmostLinearSSSP.Decremental.roundedInput i j).n
                            (DecrAlmostLinearSSSP.Decremental.roundedInput i j).k
                            (DecrAlmostLinearSSSP.Decremental.roundedInput i j).graph
                            (DecrAlmostLinearSSSP.Decremental.scaleActive i j (past t))
                            (fun e =>
                              @Nat.cast.{0} ENNReal
                                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                    ENNReal.instAddCommMonoidWithOne))
                                ((DecrAlmostLinearSSSP.Decremental.roundedInput i j).weight e))
                            u v))) →
                  @LE.le.{0} ENNReal ENNReal.instLE
                    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                      (@instHMul.{0} ENNReal
                        (@Distrib.toMul.{0} ENNReal
                          (@instDistribOfSemiring.{0} ENNReal
                            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                      (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j))
                      (@Finset.sup.{0, 0} ENNReal ι ENNReal.instSemilatticeSup ENNReal.instOrderBot S B))
                    (ENNReal.ofReal
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 16)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@List.sum.{0} Real Real.instAdd Real.instZero
                            (@List.map.{0, 0} (Fin i.k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (i.weight e))
                              es))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@Nat.cast.{0} Real Real.instNatCast (@List.length.{0} (Fin i.k) es))
                            (DecrAlmostLinearSSSP.Decremental.delta i j))))))))))) ∧ (((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (current past : Finset.{0} (Fin i.k)),
      @LE.le.{0} (Finset.{0} (Fin i.k))
          (@Preorder.toLE.{0} (Finset.{0} (Fin i.k))
            (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin i.k)) (@Finset.instPartialOrder.{0} (Fin i.k))))
          current past →
        ∀ {u v : Fin i.n} {es : List.{0} (Fin i.k)},
          @DecrAlmostLinearSSSP.Decremental.Walk i.n i.k i.graph current u v es →
            (∀ (e : Fin i.k),
                @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k)) es e →
                  @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      (DecrAlmostLinearSSSP.Decremental.scale j))) →
              ∀ (B : ENNReal),
                @LE.le.{0} ENNReal ENNReal.instLE B
                    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                      (@instHMul.{0} ENNReal
                        (@Distrib.toMul.{0} ENNReal
                          (@instDistribOfSemiring.{0} ENNReal
                            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                      (ENNReal.ofReal
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 16)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
                      (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.barrierInput i j).n
                        (DecrAlmostLinearSSSP.Decremental.barrierInput i j).k
                        (DecrAlmostLinearSSSP.Decremental.barrierInput i j).graph past
                        (fun e =>
                          @Nat.cast.{0} ENNReal
                            (@AddMonoidWithOne.toNatCast.{0} ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                            ((DecrAlmostLinearSSSP.Decremental.barrierInput i j).weight e))
                        u v)) →
                  @LE.le.{0} ENNReal ENNReal.instLE
                    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                      (@instHMul.{0} ENNReal
                        (@Distrib.toMul.{0} ENNReal
                          (@instDistribOfSemiring.{0} ENNReal
                            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                      (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j)) B)
                    (ENNReal.ofReal
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 16)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@List.sum.{0} Real Real.instAdd Real.instZero
                            (@List.map.{0, 0} (Fin i.k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (i.weight e))
                              es))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@Nat.cast.{0} Real Real.instNatCast (@List.length.{0} (Fin i.k) es))
                            (DecrAlmostLinearSSSP.Decremental.delta i j)))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) {ι : Type} (S : Finset.{0} ι) (past : ι → Finset.{0} (Fin i.k)) (current : Finset.{0} (Fin i.k)),
      (∀ (t : ι),
          @Membership.mem.{0, 0} ι (Finset.{0} ι)
              (@SetLike.instMembership.{0, 0} (Finset.{0} ι) ι (@Finset.instSetLike.{0} ι)) S t →
            @LE.le.{0} (Finset.{0} (Fin i.k))
              (@Preorder.toLE.{0} (Finset.{0} (Fin i.k))
                (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin i.k)) (@Finset.instPartialOrder.{0} (Fin i.k))))
              current (past t)) →
        ∀ {u v : Fin i.n} {es : List.{0} (Fin i.k)},
          @DecrAlmostLinearSSSP.Decremental.Walk i.n i.k i.graph current u v es →
            (∀ (e : Fin i.k),
                @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k)) es e →
                  @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      (DecrAlmostLinearSSSP.Decremental.scale j))) →
              ∀ (B : ι → ENNReal),
                (∀ (t : ι),
                    @Membership.mem.{0, 0} ι (Finset.{0} ι)
                        (@SetLike.instMembership.{0, 0} (Finset.{0} ι) ι (@Finset.instSetLike.{0} ι)) S t →
                      @LE.le.{0} ENNReal ENNReal.instLE (B t)
                        (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                          (@instHMul.{0} ENNReal
                            (@Distrib.toMul.{0} ENNReal
                              (@instDistribOfSemiring.{0} ENNReal
                                (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                          (ENNReal.ofReal
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                                (@OfNat.ofNat.{0} Real (nat_lit 16)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
                          (@DecrAlmostLinearSSSP.Decremental.distance
                            (DecrAlmostLinearSSSP.Decremental.barrierInput i j).n
                            (DecrAlmostLinearSSSP.Decremental.barrierInput i j).k
                            (DecrAlmostLinearSSSP.Decremental.barrierInput i j).graph (past t)
                            (fun e =>
                              @Nat.cast.{0} ENNReal
                                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                    ENNReal.instAddCommMonoidWithOne))
                                ((DecrAlmostLinearSSSP.Decremental.barrierInput i j).weight e))
                            u v))) →
                  @LE.le.{0} ENNReal ENNReal.instLE
                    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                      (@instHMul.{0} ENNReal
                        (@Distrib.toMul.{0} ENNReal
                          (@instDistribOfSemiring.{0} ENNReal
                            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                      (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j))
                      (@Finset.sup.{0, 0} ENNReal ι ENNReal.instSemilatticeSup ENNReal.instOrderBot S B))
                    (ENNReal.ofReal
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 16)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@List.sum.{0} Real Real.instAdd Real.instZero
                            (@List.map.{0, 0} (Fin i.k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (i.weight e))
                              es))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@Nat.cast.{0} Real Real.instNatCast (@List.length.{0} (Fin i.k) es))
                            (DecrAlmostLinearSSSP.Decremental.delta i j))))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n)
  (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
  Iff
    (@Eq.{1} Bool
      (DecrAlmostLinearSSSP.Decremental.eligible i b v (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
      Bool.true)
    (@LE.le.{0} ENNReal ENNReal.instLE
      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
        (@instHMul.{0} ENNReal
          (@Distrib.toMul.{0} ENNReal
            (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
        (ENNReal.ofReal
          (DecrAlmostLinearSSSP.Decremental.delta i (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
        (b j v))
      (ENNReal.ofReal
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (DecrAlmostLinearSSSP.Decremental.scale (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n) (p : Nat) (d : Real),
      DecrAlmostLinearSSSP.Decremental.PointerValid i b v p →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) d →
          @LE.le.{0} Real Real.instLE d
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast i.n) (@Nat.cast.{0} Real Real.instNatCast i.W)) →
            (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                @LE.le.{0} ENNReal ENNReal.instLE (ENNReal.ofReal d)
                  (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                    (@instHMul.{0} ENNReal
                      (@Distrib.toMul.{0} ENNReal
                        (@instDistribOfSemiring.{0} ENNReal
                          (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                    (ENNReal.ofReal
                      (DecrAlmostLinearSSSP.Decremental.delta i
                        (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                    (b j v))) →
              (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                  @LE.le.{0} ENNReal ENNReal.instLE (ENNReal.ofReal d)
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (DecrAlmostLinearSSSP.Decremental.scale
                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))) →
                    @LE.le.{0} ENNReal ENNReal.instLE
                      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                        (@instHMul.{0} ENNReal
                          (@Distrib.toMul.{0} ENNReal
                            (@instDistribOfSemiring.{0} ENNReal
                              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                        (ENNReal.ofReal
                          (DecrAlmostLinearSSSP.Decremental.delta i
                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                        (b j v))
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                              (@OfNat.ofNat.{0} Real (nat_lit 16)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) d
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) i.accuracy
                                (DecrAlmostLinearSSSP.Decremental.scale
                                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                              (@OfNat.ofNat.{0} Real (nat_lit 128)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126)))))))))))) →
                ∃ (h : @LT.lt.{0} Nat instLTNat p (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                  And
                    (@LE.le.{0} ENNReal ENNReal.instLE (ENNReal.ofReal d)
                      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                        (@instHMul.{0} ENNReal
                          (@Distrib.toMul.{0} ENNReal
                            (@instDistribOfSemiring.{0} ENNReal
                              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                        (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i p))
                        (b (@Fin.mk (DecrAlmostLinearSSSP.Decremental.scaleCount i) p h) v)))
                    (@LE.le.{0} ENNReal ENNReal.instLE
                      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                        (@instHMul.{0} ENNReal
                          (@Distrib.toMul.{0} ENNReal
                            (@instDistribOfSemiring.{0} ENNReal
                              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                        (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i p))
                        (b (@Fin.mk (DecrAlmostLinearSSSP.Decremental.scaleCount i) p h) v))
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                              (@OfNat.ofNat.{0} Real (nat_lit 8)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
                          d)))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n) (p : Nat),
  DecrAlmostLinearSSSP.Decremental.PointerValid i b v p →
    (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
        @LE.le.{0} ENNReal ENNReal.instLE (@Top.top.{0} ENNReal ENNReal.instTop)
          (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
            (@instHMul.{0} ENNReal
              (@Distrib.toMul.{0} ENNReal
                (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
            (ENNReal.ofReal
              (DecrAlmostLinearSSSP.Decremental.delta i (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
            (b j v))) →
      @Eq.{1} Nat p (DecrAlmostLinearSSSP.Decremental.scaleCount i)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n) (p : Nat) (d : Real),
      DecrAlmostLinearSSSP.Decremental.PointerValid i b v p →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) d →
          @LE.le.{0} Real Real.instLE d
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@Nat.cast.{0} Real Real.instNatCast i.n) (@Nat.cast.{0} Real Real.instNatCast i.W)) →
            (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                @Eq.{1} Bool
                    (DecrAlmostLinearSSSP.Decremental.eligible i b v
                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                    Bool.true →
                  @LE.le.{0} ENNReal ENNReal.instLE (ENNReal.ofReal d)
                    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                      (@instHMul.{0} ENNReal
                        (@Distrib.toMul.{0} ENNReal
                          (@instDistribOfSemiring.{0} ENNReal
                            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                      (ENNReal.ofReal
                        (DecrAlmostLinearSSSP.Decremental.delta i
                          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                      (b j v))) →
              (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                  @LE.le.{0} ENNReal ENNReal.instLE (ENNReal.ofReal d)
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (DecrAlmostLinearSSSP.Decremental.scale
                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))) →
                    @LE.le.{0} ENNReal ENNReal.instLE
                      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                        (@instHMul.{0} ENNReal
                          (@Distrib.toMul.{0} ENNReal
                            (@instDistribOfSemiring.{0} ENNReal
                              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                        (ENNReal.ofReal
                          (DecrAlmostLinearSSSP.Decremental.delta i
                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                        (b j v))
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                              (@OfNat.ofNat.{0} Real (nat_lit 16)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) d
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) i.accuracy
                                (DecrAlmostLinearSSSP.Decremental.scale
                                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                              (@OfNat.ofNat.{0} Real (nat_lit 128)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126)))))))))))) →
                ∃ (h : @LT.lt.{0} Nat instLTNat p (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                  And
                    (@LE.le.{0} ENNReal ENNReal.instLE (ENNReal.ofReal d)
                      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                        (@instHMul.{0} ENNReal
                          (@Distrib.toMul.{0} ENNReal
                            (@instDistribOfSemiring.{0} ENNReal
                              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                        (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i p))
                        (b (@Fin.mk (DecrAlmostLinearSSSP.Decremental.scaleCount i) p h) v)))
                    (@LE.le.{0} ENNReal ENNReal.instLE
                      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                        (@instHMul.{0} ENNReal
                          (@Distrib.toMul.{0} ENNReal
                            (@instDistribOfSemiring.{0} ENNReal
                              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                        (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i p))
                        (b (@Fin.mk (DecrAlmostLinearSSSP.Decremental.scaleCount i) p h) v))
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                              (@OfNat.ofNat.{0} Real (nat_lit 8)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
                          d))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n) (p : Nat),
  DecrAlmostLinearSSSP.Decremental.PointerValid i b v p →
    (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
        @Eq.{1} Bool
            (DecrAlmostLinearSSSP.Decremental.eligible i b v
              (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
            Bool.true →
          @LE.le.{0} ENNReal ENNReal.instLE (@Top.top.{0} ENNReal ENNReal.instTop)
            (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
              (@instHMul.{0} ENNReal
                (@Distrib.toMul.{0} ENNReal
                  (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
              (ENNReal.ofReal
                (DecrAlmostLinearSSSP.Decremental.delta i (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
              (b j v))) →
      @Eq.{1} Nat p (DecrAlmostLinearSSSP.Decremental.scaleCount i)) ∧ ((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Nat c.pc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Bool c.halted Bool.false →
      @Eq.{1} Bool c.fault Bool.false →
        DecrAlmostLinearSSSP.Decremental.Ends DecrAlmostLinearSSSP.Decremental.singletonProgram c
          (DecrAlmostLinearSSSP.Decremental.haltState c)) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → ENNReal)
  (s : Fin n),
  @Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.distance n k g active w s s)
    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  @Eq.{1} Nat i.n (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    ∀ (v : Fin i.n), @Eq.{1} (Fin i.n) v i.source) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (v : Fin i.n),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.initialMachine DecrAlmostLinearSSSP.Decremental.singletonProgram i).natMem
      (@Fin.val i.n v))
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (ds : List.{0} (Fin i.k)),
  ∃ cs c,
    And (DecrAlmostLinearSSSP.Decremental.OnlineRun DecrAlmostLinearSSSP.Decremental.singletonProgram i ds cs)
      (And
        (@Eq.{1} Nat (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (And
          (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
            (@List.getLast?.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine c))
          (And
            (@Eq.{1} Nat c.work
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (∀ (d : DecrAlmostLinearSSSP.Decremental.Machine),
              @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Machine
                  (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                  (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Machine) cs d →
                And
                  (∀ (v : Fin i.n),
                    @Eq.{1} Nat (d.natMem (@Fin.val i.n v))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Eq.{1} (Nat → Real) d.realMem fun x =>
                    @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @Eq.{1} Nat i.n (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      DecrAlmostLinearSSSP.Decremental.Maintains DecrAlmostLinearSSSP.Decremental.singletonProgram
        (@OfNat.ofNat.{0} Real (nat_lit 8)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
        (fun x => @OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) Bool.false i) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (active : Finset.{0} (Fin i.k)) (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal)
      (p : Fin i.n → Nat),
      (∀ (v : Fin i.n), DecrAlmostLinearSSSP.Decremental.PointerValid i b v (p v)) →
        (∀ (v : Fin i.n) (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
            @Eq.{1} Bool
                (DecrAlmostLinearSSSP.Decremental.eligible i b v
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                Bool.true →
              @LE.le.{0} ENNReal ENNReal.instLE
                (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
                  (fun e =>
                    @Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (i.weight e))
                  i.source v)
                (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                  (@instHMul.{0} ENNReal
                    (@Distrib.toMul.{0} ENNReal
                      (@instDistribOfSemiring.{0} ENNReal
                        (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                  (ENNReal.ofReal
                    (DecrAlmostLinearSSSP.Decremental.delta i
                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                  (b j v))) →
          (∀ (v : Fin i.n) (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (d : Real),
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) d →
                @Eq.{1} ENNReal
                    (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
                      (fun e =>
                        @Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (i.weight e))
                      i.source v)
                    (ENNReal.ofReal d) →
                  @LE.le.{0} ENNReal ENNReal.instLE (ENNReal.ofReal d)
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (DecrAlmostLinearSSSP.Decremental.scale
                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))) →
                    @LE.le.{0} ENNReal ENNReal.instLE
                      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                        (@instHMul.{0} ENNReal
                          (@Distrib.toMul.{0} ENNReal
                            (@instDistribOfSemiring.{0} ENNReal
                              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                        (ENNReal.ofReal
                          (DecrAlmostLinearSSSP.Decremental.delta i
                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                        (b j v))
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                              (@OfNat.ofNat.{0} Real (nat_lit 16)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) d
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) i.accuracy
                                (DecrAlmostLinearSSSP.Decremental.scale
                                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                              (@OfNat.ofNat.{0} Real (nat_lit 128)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126)))))))))))) →
            ∀ (v : Fin i.n),
              And
                (@LE.le.{0} ENNReal ENNReal.instLE
                  (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
                    (fun e =>
                      @Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (i.weight e))
                    i.source v)
                  (DecrAlmostLinearSSSP.Decremental.selected i b p v))
                (And
                  (@LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.selected i b p v)
                    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                      (@instHMul.{0} ENNReal
                        (@Distrib.toMul.{0} ENNReal
                          (@instDistribOfSemiring.{0} ENNReal
                            (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                      (ENNReal.ofReal
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) i.accuracy))
                      (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
                        (fun e =>
                          @Nat.cast.{0} ENNReal
                            (@AddMonoidWithOne.toNatCast.{0} ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                            (i.weight e))
                        i.source v)))
                  (Iff
                    (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.selected i b p v)
                      (@Top.top.{0} ENNReal ENNReal.instTop))
                    (Not (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph active i.source v)))))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (active : Finset.{0} (Fin i.k)) (u v : Fin i.n) (B : ENNReal),
      @LE.le.{0} ENNReal ENNReal.instLE
          (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.barrierInput i j).n
            (DecrAlmostLinearSSSP.Decremental.barrierInput i j).k
            (DecrAlmostLinearSSSP.Decremental.barrierInput i j).graph active
            (fun e =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                ((DecrAlmostLinearSSSP.Decremental.barrierInput i j).weight e))
            u v)
          B →
        @LE.le.{0} ENNReal ENNReal.instLE
            (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
              (@instHMul.{0} ENNReal
                (@Distrib.toMul.{0} ENNReal
                  (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
              (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j)) B)
            (ENNReal.ofReal
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (DecrAlmostLinearSSSP.Decremental.scale j))) →
          @LE.le.{0} ENNReal ENNReal.instLE
            (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
              (fun e =>
                @Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  (i.weight e))
              u v)
            (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
              (@instHMul.{0} ENNReal
                (@Distrib.toMul.{0} ENNReal
                  (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
              (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j)) B)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) {ι : Type} (S : Finset.{0} ι) (past : ι → Finset.{0} (Fin i.k)) (current : Finset.{0} (Fin i.k)),
      (∀ (t : ι),
          @Membership.mem.{0, 0} ι (Finset.{0} ι)
              (@SetLike.instMembership.{0, 0} (Finset.{0} ι) ι (@Finset.instSetLike.{0} ι)) S t →
            @LE.le.{0} (Finset.{0} (Fin i.k))
              (@Preorder.toLE.{0} (Finset.{0} (Fin i.k))
                (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin i.k)) (@Finset.instPartialOrder.{0} (Fin i.k))))
              current (past t)) →
        ∀ (u v : Fin i.n) (d : Real),
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) d →
            @Eq.{1} ENNReal
                (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph current
                  (fun e =>
                    @Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (i.weight e))
                  u v)
                (ENNReal.ofReal d) →
              @LE.le.{0} ENNReal ENNReal.instLE (ENNReal.ofReal d)
                  (ENNReal.ofReal
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      (DecrAlmostLinearSSSP.Decremental.scale j))) →
                ∀ (B : ι → ENNReal),
                  (∀ (t : ι),
                      @Membership.mem.{0, 0} ι (Finset.{0} ι)
                          (@SetLike.instMembership.{0, 0} (Finset.{0} ι) ι (@Finset.instSetLike.{0} ι)) S t →
                        @LE.le.{0} ENNReal ENNReal.instLE (B t)
                          (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                            (@instHMul.{0} ENNReal
                              (@Distrib.toMul.{0} ENNReal
                                (@instDistribOfSemiring.{0} ENNReal
                                  (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                            (ENNReal.ofReal
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                                  (@OfNat.ofNat.{0} Real (nat_lit 16)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
                            (@DecrAlmostLinearSSSP.Decremental.distance
                              (DecrAlmostLinearSSSP.Decremental.barrierInput i j).n
                              (DecrAlmostLinearSSSP.Decremental.barrierInput i j).k
                              (DecrAlmostLinearSSSP.Decremental.barrierInput i j).graph (past t)
                              (fun e =>
                                @Nat.cast.{0} ENNReal
                                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                      ENNReal.instAddCommMonoidWithOne))
                                  ((DecrAlmostLinearSSSP.Decremental.barrierInput i j).weight e))
                              u v))) →
                    @LE.le.{0} ENNReal ENNReal.instLE
                      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                        (@instHMul.{0} ENNReal
                          (@Distrib.toMul.{0} ENNReal
                            (@instDistribOfSemiring.{0} ENNReal
                              (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                        (ENNReal.ofReal (DecrAlmostLinearSSSP.Decremental.delta i j))
                        (@Finset.sup.{0, 0} ENNReal ι ENNReal.instSemilatticeSup ENNReal.instOrderBot S B))
                      (ENNReal.ofReal
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                              (@OfNat.ofNat.{0} Real (nat_lit 16)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) d
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) i.accuracy
                                (DecrAlmostLinearSSSP.Decremental.scale j))
                              (@OfNat.ofNat.{0} Real (nat_lit 128)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126))))))))))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ {ι : Type} (S : Finset.{0} ι) (past : ι → Finset.{0} (Fin i.k)) (current : Finset.{0} (Fin i.k)),
      (∀ (t : ι),
          @Membership.mem.{0, 0} ι (Finset.{0} ι)
              (@SetLike.instMembership.{0, 0} (Finset.{0} ι) ι (@Finset.instSetLike.{0} ι)) S t →
            @LE.le.{0} (Finset.{0} (Fin i.k))
              (@Preorder.toLE.{0} (Finset.{0} (Fin i.k))
                (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin i.k)) (@Finset.instPartialOrder.{0} (Fin i.k))))
              current (past t)) →
        ∀ (B : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → ι → Fin i.n → ENNReal)
          (cache : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
          (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
              @LE.le.{0} ENNReal ENNReal.instLE
                (@DecrAlmostLinearSSSP.Decremental.distance
                  (DecrAlmostLinearSSSP.Decremental.barrierInput i
                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)).n
                  (DecrAlmostLinearSSSP.Decremental.barrierInput i
                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)).k
                  (DecrAlmostLinearSSSP.Decremental.barrierInput i
                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)).graph
                  current
                  (fun e =>
                    @Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      ((DecrAlmostLinearSSSP.Decremental.barrierInput i
                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)).weight
                        e))
                  i.source v)
                (cache j v)) →
            (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
                @LE.le.{0} ENNReal ENNReal.instLE (cache j v)
                  (@Finset.sup.{0, 0} ENNReal ι ENNReal.instSemilatticeSup ENNReal.instOrderBot S fun t => B j t v)) →
              (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (t : ι),
                  @Membership.mem.{0, 0} ι (Finset.{0} ι)
                      (@SetLike.instMembership.{0, 0} (Finset.{0} ι) ι (@Finset.instSetLike.{0} ι)) S t →
                    ∀ (v : Fin i.n),
                      @LE.le.{0} ENNReal ENNReal.instLE (B j t v)
                        (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                          (@instHMul.{0} ENNReal
                            (@Distrib.toMul.{0} ENNReal
                              (@instDistribOfSemiring.{0} ENNReal
                                (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                          (ENNReal.ofReal
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                                (@OfNat.ofNat.{0} Real (nat_lit 16)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
                          (@DecrAlmostLinearSSSP.Decremental.distance
                            (DecrAlmostLinearSSSP.Decremental.barrierInput i
                                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)).n
                            (DecrAlmostLinearSSSP.Decremental.barrierInput i
                                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)).k
                            (DecrAlmostLinearSSSP.Decremental.barrierInput i
                                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)).graph
                            (past t)
                            (fun e =>
                              @Nat.cast.{0} ENNReal
                                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                    ENNReal.instAddCommMonoidWithOne))
                                ((DecrAlmostLinearSSSP.Decremental.barrierInput i
                                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)).weight
                                  e))
                            i.source v))) →
                ∀ (p : Fin i.n → Nat),
                  (∀ (v : Fin i.n), DecrAlmostLinearSSSP.Decremental.PointerValid i cache v (p v)) →
                    ∀ (v : Fin i.n),
                      And
                        (@LE.le.{0} ENNReal ENNReal.instLE
                          (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph current
                            (fun e =>
                              @Nat.cast.{0} ENNReal
                                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                    ENNReal.instAddCommMonoidWithOne))
                                (i.weight e))
                            i.source v)
                          (DecrAlmostLinearSSSP.Decremental.selected i cache p v))
                        (And
                          (@LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.selected i cache p v)
                            (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                              (@instHMul.{0} ENNReal
                                (@Distrib.toMul.{0} ENNReal
                                  (@instDistribOfSemiring.{0} ENNReal
                                    (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                              (ENNReal.ofReal
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) i.accuracy))
                              (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph current
                                (fun e =>
                                  @Nat.cast.{0} ENNReal
                                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                        ENNReal.instAddCommMonoidWithOne))
                                    (i.weight e))
                                i.source v)))
                          (Iff
                            (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.selected i cache p v)
                              (@Top.top.{0} ENNReal ENNReal.instTop))
                            (Not (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph current i.source v))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real)
      (f : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine),
      (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
          DecrAlmostLinearSSSP.Decremental.Native.InitialFacts p C a i
            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q) (f q)) →
        ∀ (v : Fin i.n),
          And
            (@LE.le.{0} ENNReal ENNReal.instLE (i.dist (@List.nil.{0} (Fin i.k)) v)
              (DecrAlmostLinearSSSP.Decremental.selected i
                (fun q v => DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                (DecrAlmostLinearSSSP.Decremental.Native.initialPointers i fun q v =>
                  DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                v))
            (And
              (@LE.le.{0} ENNReal ENNReal.instLE
                (DecrAlmostLinearSSSP.Decremental.selected i
                  (fun q v => DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                  (DecrAlmostLinearSSSP.Decremental.Native.initialPointers i fun q v =>
                    DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                  v)
                (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                  (@instHMul.{0} ENNReal
                    (@Distrib.toMul.{0} ENNReal
                      (@instDistribOfSemiring.{0} ENNReal
                        (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                  (ENNReal.ofReal
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) i.accuracy))
                  (i.dist (@List.nil.{0} (Fin i.k)) v)))
              (Iff
                (@Eq.{1} ENNReal
                  (DecrAlmostLinearSSSP.Decremental.selected i
                    (fun q v => DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                    (DecrAlmostLinearSSSP.Decremental.Native.initialPointers i fun q v =>
                      DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                    v)
                  (@Top.top.{0} ENNReal ENNReal.instTop))
                (Not
                  (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph
                    (@DecrAlmostLinearSSSP.Decremental.live i.k (@List.nil.{0} (Fin i.k))) i.source v))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve : Nat)
  (f : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Native.InitDone i p B reserve f s →
    DecrAlmostLinearSSSP.Decremental.Native.ScanTable i
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
          reserve (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).record
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
          reserve (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).cache
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
      (fun q v => DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v)) s)))))))) := by sorry
