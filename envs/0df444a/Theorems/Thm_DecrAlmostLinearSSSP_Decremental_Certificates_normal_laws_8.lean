-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_8
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:19:58.749179+00:00
-- url     : https://prove2.me/theorems/7309dbd3-a579-4a4b-85eb-bc295e17b0ad
-- title:
--   Observation invariants and linked dirty queues
-- statement:
--   Let a source program be a fixed finite deterministic scalar RAM program. Host states contain natural and real registers and memory; scaled instances, cached observations, advancing pointers and dirty queues are the objects defined by the wrapper interface.
--
--   Stored-array observations preserve historical upper and lower distance comparisons. A linked queue records dirty vertices with deduplication, so each queued vertex corresponds to a physical pending write and repeated reports do not require repeated final commits. Native linked scans and dirty-marking instructions preserve the remaining table and control state.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_8 : (((((((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.LinkedScan.body) ∧ (∀ (k : Nat),
  Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
        (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.LinkedScan.body k)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (address next : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) address →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat
          (s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          next →
        ∃ t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.LinkedScan.advance s
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) t)
            (And (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) next)
              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (vertex : Nat)
  (r : DecrAlmostLinearSSSP.Decremental.LinkedScan.Row)
  (rest : List.{0} DecrAlmostLinearSSSP.Decremental.LinkedScan.Row),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) r.address →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38)))) vertex →
      DecrAlmostLinearSSSP.Decremental.LinkedScan.RowsView s vertex
          (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.LinkedScan.Row r rest) →
        DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.LinkedScan.readRow s
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          { realReg := s.realReg,
            natReg :=
              @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                  (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) r.base)
                  (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) r.base vertex))
                (@OfNat.ofNat.{0} Nat (nat_lit 42) (instOfNatNat (nat_lit 42))) r.flag,
            realMem := s.realMem, natMem := s.natMem }))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (vertex : Nat)
  (r : DecrAlmostLinearSSSP.Decremental.LinkedScan.Row)
  (rest : List.{0} DecrAlmostLinearSSSP.Decremental.LinkedScan.Row),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) r.address →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38)))) vertex →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            DecrAlmostLinearSSSP.Decremental.LinkedScan.RowsView s vertex
                (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.LinkedScan.Row r rest) →
              ∃ cost t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.LinkedScan.body s
                    cost t)
                  (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
                    (And
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                        (@ite.{1} Nat r.Eligible (Classical.propDecidable r.Eligible) r.address
                          (DecrAlmostLinearSSSP.Decremental.LinkedScan.headAddress rest)))
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                        (@ite.{1} Nat r.Eligible (Classical.propDecidable r.Eligible)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) ∧ (∀ (rows : List.{0} DecrAlmostLinearSSSP.Decremental.LinkedScan.Row)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (vertex : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
      (DecrAlmostLinearSSSP.Decremental.LinkedScan.headAddress rows) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38)))) vertex →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            DecrAlmostLinearSSSP.Decremental.LinkedScan.RowsView s vertex rows →
              ∃ cost t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.LinkedScan.loop s
                    cost t)
                  (And
                    (@LE.le.{0} Nat instLENat cost
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                          (DecrAlmostLinearSSSP.Decremental.LinkedScan.skipped rows))
                        (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))
                    (And
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                        (DecrAlmostLinearSSSP.Decremental.LinkedScan.selectedAddress rows))
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) ∧ ((∀ (rows : List.{0} DecrAlmostLinearSSSP.Decremental.LinkedScan.Row)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (vertex : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
      (DecrAlmostLinearSSSP.Decremental.LinkedScan.headAddress rows) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38)))) vertex →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          DecrAlmostLinearSSSP.Decremental.LinkedScan.RowsView s vertex rows →
            ∃ cost t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.LinkedScan.code s
                  cost t)
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                        (DecrAlmostLinearSSSP.Decremental.LinkedScan.skipped rows))
                      (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))))
                  (And
                    (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                      (DecrAlmostLinearSSSP.Decremental.LinkedScan.selectedAddress rows))
                    (And
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem)))))) ∧ ((∀ (rows : List.{0} DecrAlmostLinearSSSP.Decremental.LinkedScan.Row),
  @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.LinkedScan.skipped rows)
    (@List.length.{0} DecrAlmostLinearSSSP.Decremental.LinkedScan.Row rows)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n) (fuel j : Nat),
  And (@LE.le.{0} Nat instLENat j (DecrAlmostLinearSSSP.Decremental.advance i b v fuel j))
    (And
      (@LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.advance i b v fuel j)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j fuel))
      (And
        (∀ (r : Nat),
          @LE.le.{0} Nat instLENat j r →
            @LT.lt.{0} Nat instLTNat r (DecrAlmostLinearSSSP.Decremental.advance i b v fuel j) →
              @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.eligible i b v r) Bool.false)
        (@LT.lt.{0} Nat instLTNat (DecrAlmostLinearSSSP.Decremental.advance i b v fuel j)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j fuel) →
          @Eq.{1} Bool
            (DecrAlmostLinearSSSP.Decremental.eligible i b v (DecrAlmostLinearSSSP.Decremental.advance i b v fuel j))
            Bool.true)))))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b c : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
  (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
      @LE.le.{0} ENNReal ENNReal.instLE (b j v) (c j v)) →
    ∀ (v : Fin i.n) (j : Nat),
      @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.eligible i b v j) Bool.false →
        @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.eligible i c v j) Bool.false) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (value : ENNReal)
  (k : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (u : Fin i.n),
  @LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i s k u)
    (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
      (DecrAlmostLinearSSSP.Decremental.adapterWrite i s j v value) k u))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (value : ENNReal) (u : Fin i.n),
  @LE.le.{0} Nat instLENat (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s u)
    (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i
      (DecrAlmostLinearSSSP.Decremental.adapterWrite i s j v value) u)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n) (p : Nat),
  @LE.le.{0} Nat instLENat p (DecrAlmostLinearSSSP.Decremental.scaleCount i) →
    (∀ (j : Nat),
        @LT.lt.{0} Nat instLTNat j p → @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.eligible i b v j) Bool.false) →
      DecrAlmostLinearSSSP.Decremental.PointerValid i b v
        (DecrAlmostLinearSSSP.Decremental.advance i b v
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (DecrAlmostLinearSSSP.Decremental.scaleCount i) p)
          p)))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n),
  DecrAlmostLinearSSSP.Decremental.PointerValid i b v
    (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i (DecrAlmostLinearSSSP.Decremental.adapterInitialize i b)
      v)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b c : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n) (j : Nat),
  (∀ (hj : @LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
      @Eq.{1} ENNReal (b (@Fin.mk (DecrAlmostLinearSSSP.Decremental.scaleCount i) j hj) v)
        (c (@Fin.mk (DecrAlmostLinearSSSP.Decremental.scaleCount i) j hj) v)) →
    @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.eligible i b v j) (DecrAlmostLinearSSSP.Decremental.eligible i c v j))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i),
  (∀ (u : Fin i.n),
      DecrAlmostLinearSSSP.Decremental.PointerValid i (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i s) u
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s u)) →
    ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (value : ENNReal) (u : Fin i.n),
      DecrAlmostLinearSSSP.Decremental.PointerValid i
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
          (DecrAlmostLinearSSSP.Decremental.adapterWrite i s j v value))
        u
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i
          (DecrAlmostLinearSSSP.Decremental.adapterWrite i s j v value) u)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v u : Fin i.n) (value : ENNReal),
  Or (@Ne.{1} (Fin i.n) u v)
      (@Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s v)
        (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)) →
    @Eq.{1} ENNReal
      (DecrAlmostLinearSSSP.Decremental.selected i
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
          (DecrAlmostLinearSSSP.Decremental.adapterWrite i s j v value))
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i
          (DecrAlmostLinearSSSP.Decremental.adapterWrite i s j v value))
        u)
      (DecrAlmostLinearSSSP.Decremental.selected i (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i s)
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s) u)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
  DecrAlmostLinearSSSP.Decremental.OutputConsistent i (DecrAlmostLinearSSSP.Decremental.adapterInitialize i b))))))) ∧ (((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i),
  DecrAlmostLinearSSSP.Decremental.OutputConsistent i s →
    ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (value : ENNReal),
      DecrAlmostLinearSSSP.Decremental.OutputConsistent i (DecrAlmostLinearSSSP.Decremental.adapterWrite i s j v value)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i),
  DecrAlmostLinearSSSP.Decremental.OutputConsistent i s →
    @Eq.{1} (Fin i.n → ENNReal)
      (@DecrAlmostLinearSSSP.Decremental.AdapterState.output i (DecrAlmostLinearSSSP.Decremental.adapterCommit i s))
      (DecrAlmostLinearSSSP.Decremental.selected i (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i s)
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n) (fuel p : Nat),
  @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.eligible i b v p) Bool.true →
    @Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.advance i b v fuel p) p) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i),
  (∀ (u : Fin i.n),
      DecrAlmostLinearSSSP.Decremental.PointerValid i (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i s) u
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s u)) →
    ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (value : ENNReal),
      @Eq.{1} (Fin i.n → Nat)
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i
          (DecrAlmostLinearSSSP.Decremental.adapterWrite i s j v value))
        (@Function.update.{1, 1} (Fin i.n) (fun a => Nat) (instDecidableEqFin i.n)
          (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s) v
          (DecrAlmostLinearSSSP.Decremental.advance i
            (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
              (DecrAlmostLinearSSSP.Decremental.adapterWrite i s j v value))
            v
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (DecrAlmostLinearSSSP.Decremental.scaleCount i)
              (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s v))
            (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s v)))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (marked : Finset.{0} (Fin i.n)),
  @LE.le.{0} (Finset.{0} (Fin i.n))
      (@Preorder.toLE.{0} (Finset.{0} (Fin i.n))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin i.n)) (@Finset.instPartialOrder.{0} (Fin i.n))))
      (@DecrAlmostLinearSSSP.Decremental.AdapterState.dirty i s) marked →
    ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (value : ENNReal),
      @LE.le.{0} (Finset.{0} (Fin i.n))
        (@Preorder.toLE.{0} (Finset.{0} (Fin i.n))
          (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin i.n)) (@Finset.instPartialOrder.{0} (Fin i.n))))
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.dirty i
          (DecrAlmostLinearSSSP.Decremental.adapterWrite i s j v value))
        (@Insert.insert.{0, 0} (Fin i.n) (Finset.{0} (Fin i.n))
          (@Finset.instInsert.{0} (Fin i.n) (instDecidableEqFin i.n)) v marked)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (marked : Finset.{0} (Fin i.n)),
  DecrAlmostLinearSSSP.Decremental.OutputConsistent i s →
    @LE.le.{0} (Finset.{0} (Fin i.n))
        (@Preorder.toLE.{0} (Finset.{0} (Fin i.n))
          (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin i.n)) (@Finset.instPartialOrder.{0} (Fin i.n))))
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.dirty i s) marked →
      @Eq.{1} (Fin i.n → ENNReal)
        (fun v =>
          @ite.{1} ENNReal
            (@Membership.mem.{0, 0} (Fin i.n) (Finset.{0} (Fin i.n))
              (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin i.n)) (Fin i.n) (@Finset.instSetLike.{0} (Fin i.n)))
              marked v)
            (@Finset.decidableMem.{0} (Fin i.n) (instDecidableEqFin i.n) v marked)
            (DecrAlmostLinearSSSP.Decremental.selected i (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i s)
              (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s) v)
            (@DecrAlmostLinearSSSP.Decremental.AdapterState.output i s v))
        (DecrAlmostLinearSSSP.Decremental.selected i (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i s)
          (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n)
  (row : Nat → DecrAlmostLinearSSSP.Decremental.LinkedScan.Row),
  (∀ (j : Nat), Iff (row j).Eligible (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.eligible i b v j) Bool.true)) →
    ∀ (fuel p : Nat),
      @Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.advance i b v fuel p)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) p
          (DecrAlmostLinearSSSP.Decremental.LinkedScan.skipped
            (DecrAlmostLinearSSSP.Decremental.LinkedScan.rowsFrom row fuel p)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n)
  (row : Nat → DecrAlmostLinearSSSP.Decremental.LinkedScan.Row) (record : Nat → Nat),
  (∀ (j : Nat), Iff (row j).Eligible (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.eligible i b v j) Bool.true)) →
    (∀ (j : Nat), @Eq.{1} Nat (row j).address (record j)) →
      ∀ (fuel p : Nat),
        @Eq.{1} Nat (record (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) p fuel))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          @Eq.{1} Nat
            (DecrAlmostLinearSSSP.Decremental.LinkedScan.selectedAddress
              (DecrAlmostLinearSSSP.Decremental.LinkedScan.rowsFrom row fuel p))
            (record (DecrAlmostLinearSSSP.Decremental.advance i b v fuel p))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (v : Fin i.n)
  (row : Nat → DecrAlmostLinearSSSP.Decremental.LinkedScan.Row),
  (∀ (j : Nat), Iff (row j).Eligible (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.eligible i b v j) Bool.true)) →
    ∀ (fuel p : Nat),
      @Eq.{1} Nat
        (DecrAlmostLinearSSSP.Decremental.LinkedScan.skipped
          (DecrAlmostLinearSSSP.Decremental.LinkedScan.rowsFrom row fuel p))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (DecrAlmostLinearSSSP.Decremental.advance i b v fuel p) p)))))) ∧ ((((∀ (r : DecrAlmostLinearSSSP.Decremental.LinkedScan.Row),
  @LE.le.{0} Nat instLENat r.flag (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r.bound →
      Iff r.Eligible
        (@LE.le.{0} ENNReal ENNReal.instLE
          (@ite.{1} ENNReal (@Eq.{1} Nat r.flag (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (instDecidableEqNat r.flag (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Top.top.{0} ENNReal ENNReal.instTop) (ENNReal.ofReal r.value))
          (ENNReal.ofReal r.bound))) ∧ (∀ (d x y : ENNReal),
  @Eq.{1} ENNReal
    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
      (@instHMul.{0} ENNReal
        (@Distrib.toMul.{0} ENNReal
          (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
      d (@Max.max.{0} ENNReal ENNReal.instMax x y))
    (@Max.max.{0} ENNReal ENNReal.instMax
      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
        (@instHMul.{0} ENNReal
          (@Distrib.toMul.{0} ENNReal
            (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
        d x)
      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
        (@instHMul.{0} ENNReal
          (@Distrib.toMul.{0} ENNReal
            (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
        d y)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (recordBase cacheBase stride : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (v : Fin i.n) (j : Nat),
  @Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.Native.scanRow i recordBase cacheBase stride s v j).address
    (DecrAlmostLinearSSSP.Decremental.Native.scanRecord i recordBase stride j)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (recordBase cacheBase stride : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
  DecrAlmostLinearSSSP.Decremental.Native.ScanTable i recordBase cacheBase stride b s →
    ∀ (v : Fin i.n) (fuel start : Nat),
      @Eq.{1} Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start fuel)
          (DecrAlmostLinearSSSP.Decremental.scaleCount i) →
        DecrAlmostLinearSSSP.Decremental.LinkedScan.RowsView s
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))
          (DecrAlmostLinearSSSP.Decremental.LinkedScan.rowsFrom
            (DecrAlmostLinearSSSP.Decremental.Native.scanRow i recordBase cacheBase stride s v) fuel start)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (recordBase cacheBase stride : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
  DecrAlmostLinearSSSP.Decremental.Native.ScanTable i recordBase cacheBase stride b s →
    ∀ (v : Fin i.n) (j : Nat),
      Iff (DecrAlmostLinearSSSP.Decremental.Native.scanRow i recordBase cacheBase stride s v j).Eligible
        (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.eligible i b v j) Bool.true))))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 42) (instOfNatNat (nat_lit 42))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 46) (instOfNatNat (nat_lit 46))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.LinkedScan.code k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))) →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.LinkedScan.code k)) ∧ ((∀ (row : Nat → DecrAlmostLinearSSSP.Decremental.LinkedScan.Row) (fuel start : Nat),
  @Eq.{1} Nat
    (@List.length.{0} DecrAlmostLinearSSSP.Decremental.LinkedScan.Row
      (DecrAlmostLinearSSSP.Decremental.LinkedScan.rowsFrom row fuel start))
    fuel) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {recordBase cacheBase stride : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal},
  DecrAlmostLinearSSSP.Decremental.Native.ScanTable i recordBase cacheBase stride b s →
    @LE.le.{0} Nat instLENat recordBase cacheBase →
      (∀ (address : Nat),
          @LE.le.{0} Nat instLENat recordBase address →
            And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
              (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
        DecrAlmostLinearSSSP.Decremental.Native.ScanTable i recordBase cacheBase stride b t) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyMark.insertCode s
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
        (DecrAlmostLinearSSSP.Decremental.DirtyMark.inserted s)))))))) ∧ ((((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyMark.prefixCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.DirtyMark.prefixData s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.DirtyMark.prefixData s).natReg
        (@OfNat.ofNat.{0} Nat (nat_lit 184) (instOfNatNat (nat_lit 184))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94)))))))
    (And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.DirtyMark.prefixData s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 188) (instOfNatNat (nat_lit 188))))
        (s.natMem
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))))))
      (∀ (k : Nat),
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 186) (instOfNatNat (nat_lit 186))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 184) (instOfNatNat (nat_lit 184))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 188) (instOfNatNat (nat_lit 188))) →
              @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.DirtyMark.prefixData s).natReg k) (s.natReg k))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.DirtyMark.prefixData s).natMem s.natMem)
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.DirtyMark.prefixData s).realMem s.realMem)) ∧ (∀ {n : Nat} (flagBase listBase : Nat) (xs : List.{0} (Fin n)) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (v : Fin n),
  @DecrAlmostLinearSSSP.Decremental.DirtyMark.View n flagBase listBase xs s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98)))) flagBase →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94)))) (@Fin.val n v) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            (∀ (u : Fin n),
                @LT.lt.{0} Nat instLTNat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flagBase
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n u)))
                  listBase) →
              ∃ cost t ys,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.DirtyMark.code s
                    cost t)
                  (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                    (And
                      (@Eq.{1} (List.{0} (Fin n)) ys
                        (@ite.{1} (List.{0} (Fin n))
                          (@Membership.mem.{0, 0} (Fin n) (List.{0} (Fin n)) (@List.instMembership.{0} (Fin n)) xs v)
                          (@List.instDecidableMemOfLawfulBEq.{0} (Fin n)
                            (@instBEqOfDecidableEq.{0} (Fin n) (instDecidableEqFin n))
                            (@Std.LawfulBEqOrd.lawfulBEq.{0} (Fin n)
                              (@instBEqOfDecidableEq.{0} (Fin n) (instDecidableEqFin n)) (instOrdFin n)
                              (@Std.LawfulBCmp.toLawfulBEqCmp.{0} (Fin n)
                                (@Preorder.toLE.{0} (Fin n)
                                  (@PartialOrder.toPreorder.{0} (Fin n)
                                    (@LinearOrder.toPartialOrder.{0} (Fin n) (@Fin.instLinearOrder n))))
                                (@Preorder.toLT.{0} (Fin n)
                                  (@PartialOrder.toPreorder.{0} (Fin n)
                                    (@LinearOrder.toPartialOrder.{0} (Fin n) (@Fin.instLinearOrder n))))
                                (@instBEqOfDecidableEq.{0} (Fin n) (instDecidableEqFin n))
                                (@Ord.compare.{0} (Fin n) (instOrdFin n))
                                (@instLawfulBCmpCompare_mathlib.{0} (Fin n) (@Fin.instLinearOrder n)))
                              (Fin.instLawfulEqOrd n))
                            v xs)
                          xs
                          (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin n)) (List.{0} (Fin n)) (List.{0} (Fin n))
                            (@instHAppendOfAppend.{0} (List.{0} (Fin n)) (@List.instAppend.{0} (Fin n))) xs
                            (@List.cons.{0} (Fin n) v (@List.nil.{0} (Fin n))))))
                      (And (@DecrAlmostLinearSSSP.Decremental.DirtyMark.View n flagBase listBase ys t)
                        (And (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin n) ys) n)
                          (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                            (∀ (address : Nat),
                              @Ne.{1} Nat address
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) flagBase
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n v))) →
                                @Ne.{1} Nat address
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) listBase
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                        (@List.length.{0} (Fin n) xs))) →
                                  @Eq.{1} Nat (t.natMem address) (s.natMem address)))))))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.pointerPrefix s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Native.pointerPrefixData s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.pointerSuffix s
    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
    (DecrAlmostLinearSSSP.Decremental.Native.pointerSuffixData s))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.pointerStart s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Native.pointerStartData s)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.Native.pointerPrefixData s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Native.pointerPrefixData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94)))))))
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Native.pointerPrefixData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Native.pointerSuffixData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Native.pointerSuffixData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.Native.pointerSuffixData s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (And
              (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Native.pointerSuffixData s).natMem
                (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                  (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                    (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))))
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))))
              (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Native.pointerSuffixData s).realMem s.realMem))))))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (recordBase cacheBase stride : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (v : Fin i.n),
  @Eq.{1} Nat
    (DecrAlmostLinearSSSP.Decremental.LinkedScan.headAddress
      (DecrAlmostLinearSSSP.Decremental.LinkedScan.rowsFrom
        (DecrAlmostLinearSSSP.Decremental.Native.scanRow i recordBase cacheBase stride s v)
        (DecrAlmostLinearSSSP.Decremental.scaleCount i) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    recordBase) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (recordBase cacheBase stride : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
  DecrAlmostLinearSSSP.Decremental.Native.ScanTable i recordBase cacheBase stride b s →
    ∀ (v : Fin i.n),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))) recordBase →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v)) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
              ∃ cost t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.LinkedScan.code s
                    cost t)
                  (And
                    (@LE.le.{0} Nat instLENat cost
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                          (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                        (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))))
                    (And
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
                        (DecrAlmostLinearSSSP.Decremental.Native.scanRecord i recordBase stride
                          (DecrAlmostLinearSSSP.Decremental.advance i b v
                            (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                      (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem)))))) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Native.pointerPrefix k) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 184) (instOfNatNat (nat_lit 184))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Native.pointerSuffix k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 42) (instOfNatNat (nat_lit 42))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 46) (instOfNatNat (nat_lit 46))) →
                  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 184) (instOfNatNat (nat_lit 184))) →
                    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))) →
                      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))) →
                        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))) →
                          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                            DecrAlmostLinearSSSP.Decremental.Native.pointerBody k)))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (recordBase cacheBase stride : Nat)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (v : Fin i.n),
  DecrAlmostLinearSSSP.Decremental.Native.ScanTable i recordBase cacheBase stride b s →
    @LE.le.{0} Nat instLENat recordBase cacheBase →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94)))) (@Fin.val i.n v) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84)))) recordBase →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                    ∃ cost t,
                      And
                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                          DecrAlmostLinearSSSP.Decremental.Native.pointerBody s cost t)
                        (And
                          (@LE.le.{0} Nat instLENat cost
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                              (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))))
                          (And
                            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val i.n v)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            (And
                              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              (And
                                (@Eq.{1} Nat
                                  (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))))
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                (And
                                  (@Eq.{1} (Nat → Nat) t.natMem
                                    (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                                      (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                                        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              (@Fin.val i.n v)))
                                          (DecrAlmostLinearSSSP.Decremental.Native.scanRecord i recordBase stride
                                            (DecrAlmostLinearSSSP.Decremental.advance i b v
                                              (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                            (@Fin.val i.n v)))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))))
                                      (@Fin.val i.n v)))
                                  (@Eq.{1} (Nat → Real) t.realMem s.realMem))))))) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Native.pointerPrefix k)) ∧ ((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Native.pointerSuffix k) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))) →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Native.pointerBody k) ∧ (DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.Native.pointerBody)))))) ∧ (((((∀ {record pointer flags list cost : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.pointerBody s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.PointerBases record pointer flags list t) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.LinkedScan.code)) ∧ ((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.Native.pointerPrefix) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.Native.pointerSuffix))) ∧ (((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.Native.pointerBody) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.Native.pointerLoop)) ∧ ((∀ {B n S reserve N address : Nat},
  DecrAlmostLinearSSSP.Decremental.Native.PointerArrayCell
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N) n address →
    @LT.lt.{0} Nat instLTNat address (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).record) ∧ ((∀ {B n S reserve N address : Nat},
  DecrAlmostLinearSSSP.Decremental.Native.PointerArrayCell
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N) n address →
    @LT.lt.{0} Nat instLTNat B address) ∧ (∀ {B n S reserve N address : Nat},
  DecrAlmostLinearSSSP.Decremental.Native.PointerArrayCell
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N) n address →
    ∃ a,
      @Eq.{1} Nat address
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) ∧ ((((∀ (B n S reserve N : Nat),
  And
    (@LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).record
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).cache)
    (And
      (∀ (v : Nat),
        @LT.lt.{0} Nat instLTNat v n →
          @LT.lt.{0} Nat instLTNat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).pointer
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v))
            (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).flags)
      (And
        (∀ (v : Nat),
          @LT.lt.{0} Nat instLTNat v n →
            @LT.lt.{0} Nat instLTNat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).flags
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v))
              (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).list)
        (∀ (v : Nat),
          @LT.lt.{0} Nat instLTNat v n →
            @LT.lt.{0} Nat instLTNat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).list
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v))
              (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).record)))) ∧ (∀ (l : DecrAlmostLinearSSSP.Decremental.Native.PointerLayout) (n : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data), DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s s)) ∧ ((∀ {l : DecrAlmostLinearSSSP.Decremental.Native.PointerLayout} {n : Nat}
  {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s t →
    DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n t u →
      DecrAlmostLinearSSSP.Decremental.Native.PublicFrame l n s u) ∧ ((∀ {B n S reserve N address : Nat},
  @LE.le.{0} Nat instLENat n B →
    DecrAlmostLinearSSSP.Decremental.Native.PublicCell
        (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N) n address →
      @LT.lt.{0} Nat instLTNat address (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N).record) ∧ (∀ {B n S reserve N j v address : Nat},
  @LE.le.{0} Nat instLENat n B →
    DecrAlmostLinearSSSP.Decremental.Native.PublicCell
        (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B n S reserve N) n address →
      @Ne.{1} Nat address (DecrAlmostLinearSSSP.Decremental.bankAddress B j v))))) ∧ (((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B S reserve j next : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine}
  {b : Fin i.n → ENNReal},
  DecrAlmostLinearSSSP.Decremental.Native.PublicFrame
      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n S reserve
        (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
      i.n s t →
    @LE.le.{0} Nat instLENat i.n B →
      DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B j
          (DecrAlmostLinearSSSP.Decremental.Native.recordAt
            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n S reserve
                (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).records
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
            j)
          (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n S reserve
                (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
            i.n j)
          next g b s →
        DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B j
          (DecrAlmostLinearSSSP.Decremental.Native.recordAt
            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n S reserve
                (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).records
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
            j)
          (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n S reserve
                (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
            i.n j)
          next g b t) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B reserve N : Nat)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (done : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Native.PointerPrefix i B reserve N b done s →
    @LT.lt.{0} Nat instLTNat done i.n →
      ∃ cost t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.pointerBody s cost
            t)
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                  (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))))
            (And
              (DecrAlmostLinearSSSP.Decremental.Native.PointerPrefix i B reserve N b
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) done
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                t)
              (DecrAlmostLinearSSSP.Decremental.Native.PublicFrame
                (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                  (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N)
                i.n s t))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B reserve N : Nat)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (done : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Native.PointerPrefix i B reserve N b done s →
    ∃ cost t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.pointerLoop s cost t)
        (And (DecrAlmostLinearSSSP.Decremental.Native.PointerPrefix i B reserve N b i.n t)
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                    (@OfNat.ofNat.{0} Nat (nat_lit 28) (instOfNatNat (nat_lit 28))))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) i.n done))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (DecrAlmostLinearSSSP.Decremental.Native.PublicFrame
              (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N)
              i.n s t)))) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Native.pointerStart k) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Native.pointerStart k)))))))) := by sorry
