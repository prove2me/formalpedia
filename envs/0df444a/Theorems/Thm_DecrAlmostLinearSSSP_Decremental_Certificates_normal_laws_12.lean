-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_12
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:20:09.948452+00:00
-- url     : https://prove2.me/theorems/2fe883df-a82d-4af9-b101-d93b519e41b1
-- title:
--   Per-scale traversal and historical observations
-- statement:
--   Let a source program be a fixed finite deterministic scalar RAM program. Host states contain natural and real registers and memory; scaled instances, cached observations, advancing pointers and dirty queues are the objects defined by the wrapper interface.
--
--   Traversal over the scaled instances composes their native deletion calls, event decoding and cache updates. The resulting event prefix agrees with the chronological source-write trace. Historical observation and pointer-energy contracts charge source instructions, report processing, deduplicated dirty work and advancing pointers across a completed update.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_12 : (((((((∀ (N B bank start : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (reports : List.{0} Nat),
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (DecrAlmostLinearSSSP.Decremental.bankFactor bank) s g →
    DecrAlmostLinearSSSP.Decremental.ReportLog start reports s →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
        (∃ r,
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
          @LT.lt.{0} Nat instLTNat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
              start →
            ∃ t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  (DecrAlmostLinearSSSP.Decremental.SourceSnapshot.code N) s
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  t)
                (And
                  (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (DecrAlmostLinearSSSP.Decremental.bankFactor bank) t
                    g)
                  (And (DecrAlmostLinearSSSP.Decremental.ReportLog start reports t)
                    (And
                      (@Eq.{1} Nat
                        (t.natMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                        g.work)
                      (And
                        (∀ (j : Nat),
                          @LT.lt.{0} Nat instLTNat j N →
                            And
                              (@Eq.{1} Nat
                                (t.natMem
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (DecrAlmostLinearSSSP.Decremental.bankFactor bank) (g.natReg j)))
                              (@Eq.{1} Real
                                (t.realMem
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                                (g.realReg j)))
                        (∀ (address : Nat),
                          @Ne.{1} Nat address
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
                            (∀ (j : Nat),
                                @LT.lt.{0} Nat instLTNat j N →
                                  @Ne.{1} Nat address
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))) →
                              And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))) ∧ (∀ (N entry : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            (DecrAlmostLinearSSSP.Decremental.ObservedSourceCall.code N entry p) k)) ∧ ((∀ (N entry : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
        (DecrAlmostLinearSSSP.Decremental.ObservedSourceCall.code N entry p) k) ∧ (∀ (N entry B bank start : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (p : DecrAlmostLinearSSSP.Decremental.Program) (g final : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
        (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Nat g.pc entry →
          @Eq.{1} Nat
              (s.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
              g.work →
            @Eq.{1} Bool g.halted Bool.false →
              @Eq.{1} Bool g.fault Bool.false →
                (∀ (a : Nat),
                    @Eq.{1} Real
                      (s.realMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (g.realMem a)) →
                  (∀ (a : Nat),
                      @Eq.{1} Nat
                        (s.natMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (DecrAlmostLinearSSSP.Decremental.bankFactor bank) (g.natMem a))) →
                    (∀ (j : Nat),
                        @LT.lt.{0} Nat instLTNat j N →
                          And
                            (@Eq.{1} Nat
                              (s.natMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (DecrAlmostLinearSSSP.Decremental.bankFactor bank) (g.natReg j)))
                            (@Eq.{1} Real
                              (s.realMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                              (g.realReg j))) →
                      (∀ (j : Nat),
                          @LE.le.{0} Nat instLENat N j →
                            And
                              (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                        DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N g →
                          DecrAlmostLinearSSSP.Decremental.Ends p g final →
                            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                              DecrAlmostLinearSSSP.Decremental.ReportLog start (@List.nil.{0} Nat) s →
                                (∃ r,
                                    @Eq.{1} Nat start
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
                                    (∃ r,
                                        @Eq.{1} Nat
                                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                      @LT.lt.{0} Nat instLTNat
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                          start →
                                        ∃ cost steps t,
                                          And
                                            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                              (DecrAlmostLinearSSSP.Decremental.ObservedSourceCall.transaction N entry
                                                p)
                                              s cost t)
                                            (And
                                              (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                                (DecrAlmostLinearSSSP.Decremental.execute p g steps) final)
                                              (And
                                                (@Eq.{1} Nat steps
                                                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                                    final.work g.work))
                                                (And
                                                  (@LE.le.{0} Nat instLENat cost
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (DecrAlmostLinearSSSP.Decremental.observedDispatchCharge
                                                              p.code)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2))))
                                                          (@HSub.hSub.{0, 0, 0} Nat Nat Nat
                                                            (@instHSub.{0} Nat instSubNat) final.work g.work))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                                                          N))
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))
                                                  (And
                                                    (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                                                      (DecrAlmostLinearSSSP.Decremental.bankFactor bank) t final)
                                                    (And
                                                      (DecrAlmostLinearSSSP.Decremental.ReportLog start
                                                        (DecrAlmostLinearSSSP.Decremental.physicalTraceWrites B bank p g
                                                          steps)
                                                        t)
                                                      (And
                                                        (@Eq.{1} Nat
                                                          (t.natMem
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (s.natReg
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 106)
                                                                  (instOfNatNat (nat_lit 106))))
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 6)
                                                                (instOfNatNat (nat_lit 6)))))
                                                          final.work)
                                                        (And
                                                          (∀ (j : Nat),
                                                            @LT.lt.{0} Nat instLTNat j N →
                                                              And
                                                                (@Eq.{1} Nat
                                                                  (t.natMem
                                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                      (@instHAdd.{0} Nat instAddNat)
                                                                      (s.natReg
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 50)
                                                                          (instOfNatNat (nat_lit 50))))
                                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                        (@instHMul.{0} Nat instMulNat)
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                          (instOfNatNat (nat_lit 2)))
                                                                        j)))
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                                    (final.natReg j)))
                                                                (@Eq.{1} Real
                                                                  (t.realMem
                                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                      (@instHAdd.{0} Nat instAddNat)
                                                                      (s.natReg
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 50)
                                                                          (instOfNatNat (nat_lit 50))))
                                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                        (@instHMul.{0} Nat instMulNat)
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                          (instOfNatNat (nat_lit 2)))
                                                                        j)))
                                                                  (final.realReg j)))
                                                          (∀ (address : Nat),
                                                            (∀ (a : Nat),
                                                                @Ne.{1} Nat address
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) B
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat)
                                                                      (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                        (@instHAdd.{0} Nat instAddNat)
                                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                          (@instHMul.{0} Nat instMulNat)
                                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                            (instOfNatNat (nat_lit 2)))
                                                                          a)
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                          (instOfNatNat (nat_lit 1))))))) →
                                                              (∀ (j : Nat),
                                                                  @LE.le.{0} Nat instLENat j
                                                                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat
                                                                        (@instHSub.{0} Nat instSubNat) final.work
                                                                        g.work) →
                                                                    @Ne.{1} Nat address
                                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                        (@instHAdd.{0} Nat instAddNat) start
                                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                          (@instHMul.{0} Nat instMulNat)
                                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                            (instOfNatNat (nat_lit 2)))
                                                                          j))) →
                                                                @Ne.{1} Nat address
                                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                      (@instHAdd.{0} Nat instAddNat)
                                                                      (s.natReg
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 106)
                                                                          (instOfNatNat (nat_lit 106))))
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 6)
                                                                        (instOfNatNat (nat_lit 6)))) →
                                                                  (∀ (j : Nat),
                                                                      @LT.lt.{0} Nat instLTNat j N →
                                                                        @Ne.{1} Nat address
                                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                            (@instHAdd.{0} Nat instAddNat)
                                                                            (s.natReg
                                                                              (@OfNat.ofNat.{0} Nat (nat_lit 50)
                                                                                (instOfNatNat (nat_lit 50))))
                                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                              (@instHMul.{0} Nat instMulNat)
                                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                                (instOfNatNat (nat_lit 2)))
                                                                              j))) →
                                                                    And
                                                                      (@Eq.{1} Nat (t.natMem address)
                                                                        (s.natMem address))
                                                                      (@Eq.{1} Real (t.realMem address)
                                                                        (s.realMem address))))))))))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (B j record cache next utilityTail reports e : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (b : Fin i.n → ENNReal) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Native.Globals i B
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) utilityTail))
      s →
    DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B j record cache next g b s →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106)))) record →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92)))) reports →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78)))) e →
            @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast e)
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size)) →
              (∃ r,
                  @Eq.{1} Nat record
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                @LT.lt.{0} Nat instLTNat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                    cache →
                  (∀ (v : Fin i.n),
                      @LT.lt.{0} Nat instLTNat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cache
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) utilityTail))) →
                    ∃ cost t,
                      And
                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                          DecrAlmostLinearSSSP.Decremental.Native.prepareUpdate s cost t)
                        (And
                          (@LE.le.{0} Nat instLENat cost
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                    DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                    (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                              (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))))
                          (And
                            (DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B j record cache next
                              (DecrAlmostLinearSSSP.Decremental.deletionMachine p g e) b t)
                            (And
                              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                                (DecrAlmostLinearSSSP.Decremental.bankFactor j))
                              (And
                                (@Eq.{1} Nat
                                  (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108)))) cache)
                                (And
                                  (@Eq.{1} Real
                                    (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))))
                                    (DecrAlmostLinearSSSP.Decremental.delta i j))
                                  (And
                                    (@Eq.{1} Nat
                                      (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
                                    (And (DecrAlmostLinearSSSP.Decremental.ReportLog reports (@List.nil.{0} Nat) t)
                                      (And
                                        (@Eq.{1} Nat
                                          (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (∀ (address : Nat),
                                          @Ne.{1} Nat address
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                                                (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))) →
                                            (∀ (a : Nat),
                                                @Ne.{1} Nat address
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          utilityTail))
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                        a))
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                              And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))))))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j : Nat}
  {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N j s t →
    DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N j t u →
      DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N j s u)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B reserve N : Nat)
  (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (r : Nat),
  @LT.lt.{0} Nat instLTNat r
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
    @LT.lt.{0} Nat instLTNat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
      (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
          N).reports) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j address : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N j s t →
    (∃ r,
        @Eq.{1} Nat address
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      @LT.lt.{0} Nat instLTNat address
          (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
              reserve N).reports →
        @Ne.{1} Nat address
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N j)
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
          (∀ (r : Nat),
              @LT.lt.{0} Nat instLTNat r N →
                @Ne.{1} Nat address
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N j)
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))) →
            And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
              (@Eq.{1} Real (t.realMem address) (s.realMem address))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B reserve N : Nat)
  (q j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (r : Nat),
  @LE.le.{0} Nat instLENat r (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
    And
      (@Ne.{1} Nat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
      (∀ (t : Nat),
        @LT.lt.{0} Nat instLTNat t N →
          @Ne.{1} Nat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t)))))))) ∧ ((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat}
  {j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N
      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t →
    ∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (r : Nat),
      @LE.le.{0} Nat instLENat r (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        And
          (@Eq.{1} Nat
            (t.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)))
            (s.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))))
          (@Eq.{1} Real
            (t.realMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)))
            (s.realMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat}
  {j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N
      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t →
    ∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
      And
        (@Eq.{1} Nat
          (t.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).caches
                i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
          (s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).caches
                i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v)))))
        (@Eq.{1} Real
          (t.realMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).caches
                i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))
          (s.realMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).caches
                i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val i.n v))))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N address : Nat}
  {j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N
      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t →
    DecrAlmostLinearSSSP.Decremental.Native.PointerArrayCell
        (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
          reserve N)
        i.n address →
      And (@Eq.{1} Nat (t.natMem address) (s.natMem address)) (@Eq.{1} Real (t.realMem address) (s.realMem address))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N address : Nat}
  {j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N
      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t →
    @LE.le.{0} Nat instLENat address B →
      And (@Eq.{1} Nat (t.natMem address) (s.natMem address)) (@Eq.{1} Real (t.realMem address) (s.realMem address))))) ∧ (((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat}
  {j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)} {a : DecrAlmostLinearSSSP.Decremental.AdapterState i}
  {xs : List.{0} (Fin i.n)} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
    @LE.le.{0} Nat instLENat i.n B →
      DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N
          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t →
        @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182)))) →
          @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180)))) →
            DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs t) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.Native.CacheRefresh.code)) ∧ ((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.Native.PointerRefresh.code) ∧ ((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.DirtyMark.code) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.ReportDecode.code)))))) ∧ (((((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.Native.decodedReportEvent) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.code)) ∧ ((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) →
                  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) →
                    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) →
                      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 208) (instOfNatNat (nat_lit 208))) →
                        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
                          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                            DecrAlmostLinearSSSP.Decremental.Native.prepareUpdate k) ∧ (∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) →
            DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Native.prepareUpdate
              k))) ∧ (((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B utility cost : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.prepareUpdate s cost t →
      @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility t) ∧ (∀ (N entry : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            (DecrAlmostLinearSSSP.Decremental.ObservedSourceCall.transaction N entry p) k)) ∧ ((∀ (N entry : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
        (DecrAlmostLinearSSSP.Decremental.ObservedSourceCall.transaction N entry p) k) ∧ ((∀ (N entry : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame
    (DecrAlmostLinearSSSP.Decremental.ObservedSourceCall.transaction N entry p)) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.Native.prepareUpdate))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (e : Fin i.k)
          (g final : DecrAlmostLinearSSSP.Decremental.Machine) (a : DecrAlmostLinearSSSP.Decremental.AdapterState i)
          (xs : List.{0} (Fin i.n)) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          DecrAlmostLinearSSSP.Decremental.Native.Globals i B
              (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                  reserve (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).utility
              s →
            DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve
                (DecrAlmostLinearSSSP.Decremental.registerBound p.code) a xs s →
              DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)
                  (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve
                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
                    (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                  (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                    (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                        (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                        (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
                    i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                  (DecrAlmostLinearSSSP.Decremental.Native.nextRecord
                    (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                        (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                        (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).records
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                    (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                  g (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a j) s →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                    (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve
                      (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92))))
                      (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                          (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                          (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).reports →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))
                        (@Fin.val i.k e) →
                      (∀ (r : Nat),
                          @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code) r →
                            And
                              (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                        DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail
                            (DecrAlmostLinearSSSP.Decremental.registerBound p.code) g →
                          DecrAlmostLinearSSSP.Decremental.Ends p
                              (DecrAlmostLinearSSSP.Decremental.deletionMachine p g (@Fin.val i.k e)) final →
                            @LE.le.{0} Nat instLENat final.work reserve →
                              ∃ cost steps t,
                                And
                                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                    (DecrAlmostLinearSSSP.Decremental.Native.sourceUpdate p) s cost t)
                                  (And
                                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                      (DecrAlmostLinearSSSP.Decremental.execute p
                                        (DecrAlmostLinearSSSP.Decremental.deletionMachine p g (@Fin.val i.k e)) steps)
                                      final)
                                    (And
                                      (@Eq.{1} Nat steps
                                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) final.work
                                          g.work))
                                      (And
                                        (@LE.le.{0} Nat instLENat cost
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                                      DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                                      (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (DecrAlmostLinearSSSP.Decremental.observedDispatchCharge p.code)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                                    final.work g.work)))
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                                                (DecrAlmostLinearSSSP.Decremental.registerBound p.code)))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34)))))
                                        (And
                                          (DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve
                                            (DecrAlmostLinearSSSP.Decremental.registerBound p.code) a xs t)
                                          (And
                                            (DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B
                                              (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)
                                              (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve
                                                (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
                                                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                                              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                                                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                                                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
                                                i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                                              (DecrAlmostLinearSSSP.Decremental.Native.nextRecord
                                                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                                                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).records
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                                (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                                                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                                              final (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a j) t)
                                            (And
                                              (DecrAlmostLinearSSSP.Decremental.Native.Globals i B
                                                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                                                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).utility
                                                t)
                                              (And
                                                (@Eq.{1} Nat
                                                  (t.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                                                  (DecrAlmostLinearSSSP.Decremental.bankFactor
                                                    (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                                                (And
                                                  (@Eq.{1} Nat
                                                    (t.natReg
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108))))
                                                    (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                                                      (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                                                          (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                                          (DecrAlmostLinearSSSP.Decremental.registerBound
                                                            p.code)).caches
                                                      i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                                                  (And
                                                    (@Eq.{1} Real
                                                      (t.realReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))))
                                                      (DecrAlmostLinearSSSP.Decremental.delta i
                                                        (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)))
                                                    (And
                                                      (DecrAlmostLinearSSSP.Decremental.ReportLog
                                                        (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                                                            (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                                            (DecrAlmostLinearSSSP.Decremental.registerBound
                                                              p.code)).reports
                                                        (DecrAlmostLinearSSSP.Decremental.physicalTraceWrites B
                                                          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) p
                                                          (DecrAlmostLinearSSSP.Decremental.deletionMachine p g
                                                            (@Fin.val i.k e))
                                                          steps)
                                                        t)
                                                      (And
                                                        (∀ (r : Nat),
                                                          @LE.le.{0} Nat instLENat
                                                              (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
                                                              r →
                                                            And
                                                              (@Eq.{1} Nat
                                                                (t.natReg
                                                                  (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                  (instOfNatNat (nat_lit 0))))
                                                              (@Eq.{1} Real
                                                                (t.realReg
                                                                  (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                                                (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                                  (@Zero.toOfNat0.{0} Real Real.instZero))))
                                                        (DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B
                                                          reserve
                                                          (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
                                                          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s
                                                          t))))))))))))) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))) k →
    @LE.le.{0} Nat instLENat k (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))) →
      @Even.{0} Nat instAddNat k →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.Native.sourceUpdate p) k)) ∧ ((∀ (D obs N elapsed raw first second travel : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) elapsed →
    @LE.le.{0} Nat instLENat raw elapsed →
      @LE.le.{0} Nat instLENat first
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) D
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) obs
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  elapsed))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N))
            (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34)))) →
        @LE.le.{0} Nat instLENat second
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) D
                    (@OfNat.ofNat.{0} Nat (nat_lit 61) (instOfNatNat (nat_lit 61))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) raw
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) travel))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
          @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) first second)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) D)
                      obs)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N))
                  (@OfNat.ofNat.{0} Nat (nat_lit 160) (instOfNatNat (nat_lit 160))))
                elapsed)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) travel))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j s t →
    ∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (r : Nat),
      @LT.lt.{0} Nat instLTNat r
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
        And
          (@Eq.{1} Nat
            (t.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)))
            (s.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))))
          (@Eq.{1} Real
            (t.realMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)))
            (s.realMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (before after : Fin i.n → ENNReal)
  (reports : List.{0} (Fin i.n)),
  (∀ (v : Fin i.n),
      @LE.le.{0} ENNReal ENNReal.instLE (before v) (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i s j v)) →
    (∀ (v : Fin i.n),
        @Ne.{1} ENNReal (after v) (before v) →
          @Membership.mem.{0, 0} (Fin i.n) (List.{0} (Fin i.n)) (@List.instMembership.{0} (Fin i.n)) reports v) →
      ∀ (v : Fin i.n),
        @LE.le.{0} ENNReal ENNReal.instLE (after v)
          (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
            (DecrAlmostLinearSSSP.Decremental.adapterTrace i s
              (@List.map.{0, 0} (Fin i.n) (DecrAlmostLinearSSSP.Decremental.AdapterEvent i)
                (fun v =>
                  @Prod.mk.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal)
                    j (@Prod.mk.{0, 0} (Fin i.n) ENNReal v (after v)))
                reports))
            j v))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (B bank : Nat)
  (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  (∀ (v : Fin i.n),
      @LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val i.n v))
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i s j v)) →
    ∀ (v : Fin i.n),
      @LE.le.{0} ENNReal ENNReal.instLE
        (DecrAlmostLinearSSSP.Decremental.stored (DecrAlmostLinearSSSP.Decremental.execute p c t) (@Fin.val i.n v))
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
          (DecrAlmostLinearSSSP.Decremental.adapterTrace i s
            (@List.map.{0, 0} (Fin i.n) (DecrAlmostLinearSSSP.Decremental.AdapterEvent i)
              (fun v =>
                @Prod.mk.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal) j
                  (@Prod.mk.{0, 0} (Fin i.n) ENNReal v
                    (DecrAlmostLinearSSSP.Decremental.stored (DecrAlmostLinearSSSP.Decremental.execute p c t)
                      (@Fin.val i.n v))))
              (DecrAlmostLinearSSSP.Decremental.publicReports i B bank
                (DecrAlmostLinearSSSP.Decremental.physicalTraceWrites B bank p c t))))
          j v)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (e : Fin i.k)
          (g final : DecrAlmostLinearSSSP.Decremental.Machine) (a : DecrAlmostLinearSSSP.Decremental.AdapterState i)
          (xs : List.{0} (Fin i.n)) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          DecrAlmostLinearSSSP.Decremental.Native.Globals i B
              (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                  reserve (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).utility
              s →
            DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve
                (DecrAlmostLinearSSSP.Decremental.registerBound p.code) a xs s →
              (∀ (v : Fin i.n),
                  DecrAlmostLinearSSSP.Decremental.PointerValid i
                    (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a) v
                    (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a v)) →
                DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B
                    (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)
                    (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve
                      (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                    (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                      (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                          (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                          (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
                      i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                    (DecrAlmostLinearSSSP.Decremental.Native.nextRecord
                      (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                          (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                          (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).records
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                    g (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a j) s →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                      (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve
                        (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
                        (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92))))
                        (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                            (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                            (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).reports →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))
                          (@Fin.val i.k e) →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
                            (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).pointer →
                          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
                              (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                  (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                  (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).flags →
                            (∀ (r : Nat),
                                @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code) r →
                                  And
                                    (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                    (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                              DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail
                                  (DecrAlmostLinearSSSP.Decremental.registerBound p.code) g →
                                DecrAlmostLinearSSSP.Decremental.Ends p
                                    (DecrAlmostLinearSSSP.Decremental.deletionMachine p g (@Fin.val i.k e)) final →
                                  @LE.le.{0} Nat instLENat final.work reserve →
                                    (∀ (v : Fin i.n),
                                        And
                                          (@LE.le.{0} Nat instLENat (final.natMem (@Fin.val i.n v))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                          (@Eq.{1} Nat (final.natMem (@Fin.val i.n v))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                                            @LE.le.{0} Real Real.instLE
                                              (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                (@Zero.toOfNat0.{0} Real Real.instZero))
                                              (final.realMem (@Fin.val i.n v)))) →
                                      ∃ cost steps t u ys,
                                        have reports :=
                                          DecrAlmostLinearSSSP.Decremental.physicalTraceWrites B
                                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) p
                                            (DecrAlmostLinearSSSP.Decremental.deletionMachine p g (@Fin.val i.k e))
                                            steps;
                                        have anew :=
                                          DecrAlmostLinearSSSP.Decremental.adapterTrace i a
                                            (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.allEvents i B j final
                                              reports);
                                        And
                                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                            (DecrAlmostLinearSSSP.Decremental.Native.scaleUpdate p) s cost t)
                                          (And
                                            (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                              (DecrAlmostLinearSSSP.Decremental.execute p
                                                (DecrAlmostLinearSSSP.Decremental.deletionMachine p g (@Fin.val i.k e))
                                                steps)
                                              final)
                                            (And
                                              (@Eq.{1} Nat steps
                                                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                                  final.work g.work))
                                              (And
                                                (@LE.le.{0} Nat instLENat cost
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (DecrAlmostLinearSSSP.Decremental.Native.scaleUpdateCharge p
                                                        i.size)
                                                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                                        final.work g.work))
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                                      (DecrAlmostLinearSSSP.Decremental.pointerTravel i a
                                                        (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.allEvents
                                                          i B j final reports)))))
                                                (And
                                                  (DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve
                                                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code) anew ys t)
                                                  (And
                                                    (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin i.n) ys)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@List.length.{0} (Fin i.n) xs) (@List.length.{0} Nat reports)))
                                                    (And
                                                      (DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B
                                                        (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)
                                                        (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B
                                                          reserve
                                                          (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
                                                          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                                                        (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                                                          (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                                                              (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                                              (DecrAlmostLinearSSSP.Decremental.registerBound
                                                                p.code)).caches
                                                          i.n
                                                          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                                                        (DecrAlmostLinearSSSP.Decremental.Native.nextRecord
                                                          (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                                                              (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                                              (DecrAlmostLinearSSSP.Decremental.registerBound
                                                                p.code)).records
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 8)
                                                              (instOfNatNat (nat_lit 8))))
                                                          (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                                                          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                                                        final
                                                        (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i anew j)
                                                        t)
                                                      (And
                                                        (DecrAlmostLinearSSSP.Decremental.Native.Globals i B
                                                          (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                                                              (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                                              (DecrAlmostLinearSSSP.Decremental.registerBound
                                                                p.code)).utility
                                                          t)
                                                        (And
                                                          (∀ (r : Nat),
                                                            @LE.le.{0} Nat instLENat
                                                                (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
                                                                r →
                                                              And
                                                                (@Eq.{1} Nat
                                                                  (t.natReg
                                                                    (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                    (instOfNatNat (nat_lit 0))))
                                                                (@Eq.{1} Real
                                                                  (t.realReg
                                                                    (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                                                  (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                                    (@Zero.toOfNat0.{0} Real Real.instZero))))
                                                          (And
                                                            (DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i
                                                              B reserve
                                                              (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
                                                              (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                                                                j)
                                                              s u)
                                                            (DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B
                                                              reserve
                                                              (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
                                                              (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                                                                j)
                                                              u t)))))))))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat}
  {j q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N
      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t →
    @Ne.{1} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) q j →
      ∀ (v : Nat),
        And
          (@Eq.{1} Nat
            (t.natMem
              (DecrAlmostLinearSSSP.Decremental.bankAddress B
                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q) v))
            (s.natMem
              (DecrAlmostLinearSSSP.Decremental.bankAddress B
                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q) v)))
          (@Eq.{1} Real
            (t.realMem
              (DecrAlmostLinearSSSP.Decremental.bankAddress B
                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q) v))
            (s.realMem
              (DecrAlmostLinearSSSP.Decremental.bankAddress B
                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q) v)))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat}
  {j q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve N
      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t →
    @Ne.{1} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) q j →
      ∀ (r : Nat),
        @LT.lt.{0} Nat instLTNat r
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
          And
            (@Eq.{1} Nat
              (t.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
                    (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)))
              (s.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
                    (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))))
            (@Eq.{1} Real
              (t.realMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
                    (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)))
              (s.realMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve N
                    (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B reserve : Nat}
  {j q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)} {next : Nat}
  {g : DecrAlmostLinearSSSP.Decremental.Machine} {b : Fin i.n → ENNReal}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve
      (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t →
    @Ne.{1} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) q j →
      DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B
          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q)
          (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve
            (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
          (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                reserve (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
            i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
          next g b s →
        DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B
          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q)
          (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve
            (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
          (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                reserve (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
            i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
          next g b t))))))) ∧ ((((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B reserve : Nat}
  {j q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)} {next : Nat}
  {g : DecrAlmostLinearSSSP.Decremental.Machine} {b c : Fin i.n → ENNReal}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve
      (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t →
    DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B
        (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q)
        (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve
          (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
        (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
          (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
              reserve (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
          i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
        next g b s →
      DecrAlmostLinearSSSP.Decremental.Native.CacheImage i (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q)
          (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                reserve (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
            i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
          c t →
        DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B
          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q)
          (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve
            (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
          (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                reserve (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
            i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
          next g c t) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B reserve : Nat}
  {f : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine}
  {a : DecrAlmostLinearSSSP.Decremental.AdapterState i} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.FamilyMemory i p B reserve f a s →
    @Eq.{1} (Nat → Nat) t.natMem s.natMem →
      @Eq.{1} (Nat → Real) t.realMem s.realMem →
        DecrAlmostLinearSSSP.Decremental.Native.FamilyMemory i p B reserve f a t)) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B reserve : Nat}
  {f : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine}
  {a b : DecrAlmostLinearSSSP.Decremental.AdapterState i} {s u t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.FamilyMemory i p B reserve f a s →
    ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (final : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Native.SourceUpdateFrame i B reserve
          (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s u →
        DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve
            (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) u t →
          (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
              DecrAlmostLinearSSSP.Decremental.Native.CacheImage i
                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q)
                (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                  (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                      (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
                  i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q))
                (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i b q) t) →
            DecrAlmostLinearSSSP.Decremental.Native.ScaleMemory i p B
                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)
                (DecrAlmostLinearSSSP.Decremental.Native.sourceRecord i B reserve
                  (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                  (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                      (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).caches
                  i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                (DecrAlmostLinearSSSP.Decremental.Native.nextRecord
                  (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                      (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).records
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                  (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                final (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i b j) t →
              DecrAlmostLinearSSSP.Decremental.Native.FamilyMemory i p B reserve
                (@Function.update.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                  (fun a => DecrAlmostLinearSSSP.Decremental.Machine)
                  (instDecidableEqFin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) f j final)
                b t) ∧ (∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      (∀ (r : Nat),
          @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
              DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.forbiddenNat r →
            @Ne.{1} Nat k r) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.code
          k))) ∧ (((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Native.PersistentControl k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.Native.scaleUpdate p) k) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame (DecrAlmostLinearSSSP.Decremental.Native.scaleUpdate p))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
  (d : Nat) (hd : @LT.lt.{0} Nat instLTNat d (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.Native.updateMachinesPrefix i before after d
      (@Fin.mk (DecrAlmostLinearSSSP.Decremental.scaleCount i) d hd))
    (before (@Fin.mk (DecrAlmostLinearSSSP.Decremental.scaleCount i) d hd))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
  (d : Nat) (hd : @LT.lt.{0} Nat instLTNat d (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
  @Eq.{1} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
    (DecrAlmostLinearSSSP.Decremental.Native.updateMachinesPrefix i before after
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@Function.update.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i))
      (fun a => DecrAlmostLinearSSSP.Decremental.Machine)
      (instDecidableEqFin (DecrAlmostLinearSSSP.Decremental.scaleCount i))
      (DecrAlmostLinearSSSP.Decremental.Native.updateMachinesPrefix i before after d)
      (@Fin.mk (DecrAlmostLinearSSSP.Decremental.scaleCount i) d hd)
      (after (@Fin.mk (DecrAlmostLinearSSSP.Decremental.scaleCount i) d hd)))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
    (DecrAlmostLinearSSSP.Decremental.Native.updateMachinesPrefix i before after
      (DecrAlmostLinearSSSP.Decremental.scaleCount i))
    after))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (B : Nat) (e : Fin i.k)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
  (d : Nat),
  @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.Native.updateReportsPrefix i p B e before after d)
    (DecrAlmostLinearSSSP.Decremental.Native.updateWorkPrefix i before after d)) ∧ (∀ (N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.start N) s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.started N s))) ∧ ((∀ (N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.started N s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.started N s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.started N s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.started N s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 134) (instOfNatNat (nat_lit 134))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) N)
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))) ∧ ((∀ (N k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 134) (instOfNatNat (nat_lit 134))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            (DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.start N) k) ∧ (∀ (N k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.start N) k)))) ∧ (((∀ (N : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NoMemory (DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.start N)) ∧ (∀ (N : Nat),
  DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame (DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.start N))) ∧ ((∀ {B n S reserve N : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.Controls B n S reserve N s →
    DecrAlmostLinearSSSP.Decremental.Native.Controls B n S reserve N
      (DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.started N s)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.advance s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.advanced s)) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
        DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.advance k)))))) ∧ (((((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.advance
    k) ∧ (DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.advance)) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame
  DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.advance) ∧ (∀ (N : Nat),
  DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.start N)))) ∧ (((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.advance) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve : Nat)
  (e : Fin i.k)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
  (a : DecrAlmostLinearSSSP.Decremental.AdapterState i) (xs : List.{0} (Fin i.n))
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Native.Globals i B
      (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
          (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).utility
      s →
    DecrAlmostLinearSSSP.Decremental.Native.Controls B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
        (DecrAlmostLinearSSSP.Decremental.registerBound p.code) s →
      DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve
          (DecrAlmostLinearSSSP.Decremental.registerBound p.code) a xs s →
        DecrAlmostLinearSSSP.Decremental.Native.FamilyMemory i p B reserve before a s →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (@Fin.val i.k e) →
            (∀ (r : Nat),
                @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code) r →
                  And
                    (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
              DecrAlmostLinearSSSP.Decremental.Native.UpdatePrefix i p B reserve e before after a
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) xs
                (DecrAlmostLinearSSSP.Decremental.Native.UpdateTraversal.started
                  (DecrAlmostLinearSSSP.Decremental.registerBound p.code) s))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (e : Fin i.k)
          (before after :
            Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
          (a : DecrAlmostLinearSSSP.Decremental.AdapterState i),
          (∀ (v : Fin i.n),
              DecrAlmostLinearSSSP.Decremental.PointerValid i
                (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a) v
                (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a v)) →
            (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail
                  (DecrAlmostLinearSSSP.Decremental.registerBound p.code) (before q)) →
              (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                  DecrAlmostLinearSSSP.Decremental.Ends p
                    (DecrAlmostLinearSSSP.Decremental.deletionMachine p (before q) (@Fin.val i.k e)) (after q)) →
                (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                    @LE.le.{0} Nat instLENat (after q).work reserve) →
                  (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
                      And
                        (@LE.le.{0} Nat instLENat ((after q).natMem (@Fin.val i.n v))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@Eq.{1} Nat ((after q).natMem (@Fin.val i.n v))
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                          @LE.le.{0} Real Real.instLE
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                            ((after q).realMem (@Fin.val i.n v)))) →
                    ∀ (d : Nat) (xs : List.{0} (Fin i.n)) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
                      DecrAlmostLinearSSSP.Decremental.Native.UpdatePrefix i p B reserve e before after a d xs s →
                        ∀ (hd : @LT.lt.{0} Nat instLTNat d (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                          ∃ cost t ys,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                (DecrAlmostLinearSSSP.Decremental.Native.scaleUpdateBody p) s cost t)
                              (And
                                (DecrAlmostLinearSSSP.Decremental.Native.UpdatePrefix i p B reserve e before after a
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                  ys t)
                                (And
                                  (@LE.le.{0} Nat instLENat cost
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (DecrAlmostLinearSSSP.Decremental.Native.scaleUpdateCharge p i.size)
                                          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                            (after (@Fin.mk (DecrAlmostLinearSSSP.Decremental.scaleCount i) d hd)).work
                                            (before
                                                (@Fin.mk (DecrAlmostLinearSSSP.Decremental.scaleCount i) d hd)).work))
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                          (DecrAlmostLinearSSSP.Decremental.pointerTravel i
                                            (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
                                              (DecrAlmostLinearSSSP.Decremental.Native.updateEventsPrefix i p B e before
                                                after d))
                                            (DecrAlmostLinearSSSP.Decremental.Native.scaleEvents i p B e before after
                                              (@Fin.mk (DecrAlmostLinearSSSP.Decremental.scaleCount i) d hd)))))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                  (And
                                    (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin i.n) ys)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@List.length.{0} (Fin i.n) xs)
                                        (@List.length.{0} Nat
                                          (DecrAlmostLinearSSSP.Decremental.Native.scaleReports i p B e before after
                                            (@Fin.mk (DecrAlmostLinearSSSP.Decremental.scaleCount i) d hd)))))
                                    (∀ (address : Nat),
                                      @LE.le.{0} Nat instLENat address B →
                                        And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                          (@Eq.{1} Real (t.realMem address) (s.realMem address))))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (e : Fin i.k)
          (before after :
            Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
          (a : DecrAlmostLinearSSSP.Decremental.AdapterState i),
          (∀ (v : Fin i.n),
              DecrAlmostLinearSSSP.Decremental.PointerValid i
                (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a) v
                (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a v)) →
            (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail
                  (DecrAlmostLinearSSSP.Decremental.registerBound p.code) (before q)) →
              (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                  DecrAlmostLinearSSSP.Decremental.Ends p
                    (DecrAlmostLinearSSSP.Decremental.deletionMachine p (before q) (@Fin.val i.k e)) (after q)) →
                (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                    @LE.le.{0} Nat instLENat (after q).work reserve) →
                  (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
                      And
                        (@LE.le.{0} Nat instLENat ((after q).natMem (@Fin.val i.n v))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@Eq.{1} Nat ((after q).natMem (@Fin.val i.n v))
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                          @LE.le.{0} Real Real.instLE
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                            ((after q).realMem (@Fin.val i.n v)))) →
                    ∀ (remaining d : Nat),
                      @Eq.{1} Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d remaining)
                          (DecrAlmostLinearSSSP.Decremental.scaleCount i) →
                        ∀ (xs : List.{0} (Fin i.n)) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
                          DecrAlmostLinearSSSP.Decremental.Native.UpdatePrefix i p B reserve e before after a d xs s →
                            ∃ cost t ys,
                              And
                                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                  (DecrAlmostLinearSSSP.Decremental.Native.scaleUpdateLoop p) s cost t)
                                (And
                                  (DecrAlmostLinearSSSP.Decremental.Native.UpdatePrefix i p B reserve e before after a
                                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) ys t)
                                  (And
                                    (@LE.le.{0} Nat instLENat
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (DecrAlmostLinearSSSP.Decremental.Native.scaleUpdateCharge p i.size)
                                              (DecrAlmostLinearSSSP.Decremental.Native.updateWorkPrefix i before after
                                                d)))
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                            (DecrAlmostLinearSSSP.Decremental.pointerTravel i a
                                              (DecrAlmostLinearSSSP.Decremental.Native.updateEventsPrefix i p B e before
                                                after d))))
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) d))
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (DecrAlmostLinearSSSP.Decremental.Native.scaleUpdateCharge p i.size)
                                              (DecrAlmostLinearSSSP.Decremental.Native.updateWorkPrefix i before after
                                                (DecrAlmostLinearSSSP.Decremental.scaleCount i)))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                              (DecrAlmostLinearSSSP.Decremental.pointerTravel i a
                                                (DecrAlmostLinearSSSP.Decremental.Native.updateEventsPrefix i p B e
                                                  before after (DecrAlmostLinearSSSP.Decremental.scaleCount i)))))
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                            (DecrAlmostLinearSSSP.Decremental.scaleCount i)))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                    (And
                                      (@LE.le.{0} Nat instLENat
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@List.length.{0} (Fin i.n) ys)
                                          (DecrAlmostLinearSSSP.Decremental.Native.updateReportsPrefix i p B e before
                                            after d))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@List.length.{0} (Fin i.n) xs)
                                          (DecrAlmostLinearSSSP.Decremental.Native.updateReportsPrefix i p B e before
                                            after (DecrAlmostLinearSSSP.Decremental.scaleCount i))))
                                      (∀ (address : Nat),
                                        @LE.le.{0} Nat instLENat address B →
                                          And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                            (@Eq.{1} Real (t.realMem address) (s.realMem address))))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (e : Fin i.k)
          (before after :
            Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
          (a : DecrAlmostLinearSSSP.Decremental.AdapterState i),
          (∀ (v : Fin i.n),
              DecrAlmostLinearSSSP.Decremental.PointerValid i
                (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a) v
                (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a v)) →
            (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail
                  (DecrAlmostLinearSSSP.Decremental.registerBound p.code) (before q)) →
              (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                  DecrAlmostLinearSSSP.Decremental.Ends p
                    (DecrAlmostLinearSSSP.Decremental.deletionMachine p (before q) (@Fin.val i.k e)) (after q)) →
                (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                    @LE.le.{0} Nat instLENat (after q).work reserve) →
                  (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
                      And
                        (@LE.le.{0} Nat instLENat ((after q).natMem (@Fin.val i.n v))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@Eq.{1} Nat ((after q).natMem (@Fin.val i.n v))
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                          @LE.le.{0} Real Real.instLE
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                            ((after q).realMem (@Fin.val i.n v)))) →
                    ∀ (xs : List.{0} (Fin i.n)) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
                      DecrAlmostLinearSSSP.Decremental.Native.Globals i B
                          (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                              (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                              (DecrAlmostLinearSSSP.Decremental.registerBound p.code)).utility
                          s →
                        DecrAlmostLinearSSSP.Decremental.Native.Controls B i.n
                            (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                            (DecrAlmostLinearSSSP.Decremental.registerBound p.code) s →
                          DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve
                              (DecrAlmostLinearSSSP.Decremental.registerBound p.code) a xs s →
                            DecrAlmostLinearSSSP.Decremental.Native.FamilyMemory i p B reserve before a s →
                              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                                  (@Fin.val i.k e) →
                                (∀ (r : Nat),
                                    @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code) r →
                                      And
                                        (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                          (@OfNat.ofNat.{0} Real (nat_lit 0)
                                            (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                                  ∃ cost t ys,
                                    And
                                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                        (DecrAlmostLinearSSSP.Decremental.Native.scaleUpdateAll p) s cost t)
                                      (And
                                        (DecrAlmostLinearSSSP.Decremental.Native.UpdatePrefix i p B reserve e before
                                          after a (DecrAlmostLinearSSSP.Decremental.scaleCount i) ys t)
                                        (And
                                          (@LE.le.{0} Nat instLENat cost
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (DecrAlmostLinearSSSP.Decremental.Native.scaleUpdateCharge p i.size)
                                                    (DecrAlmostLinearSSSP.Decremental.Native.updateWorkPrefix i before
                                                      after (DecrAlmostLinearSSSP.Decremental.scaleCount i)))
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                                    (DecrAlmostLinearSSSP.Decremental.pointerTravel i a
                                                      (DecrAlmostLinearSSSP.Decremental.Native.updateEventsPrefix i p B
                                                        e before after
                                                        (DecrAlmostLinearSSSP.Decremental.scaleCount i)))))
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  (DecrAlmostLinearSSSP.Decremental.scaleCount i)))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                                          (And
                                            (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin i.n) ys)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@List.length.{0} (Fin i.n) xs)
                                                (DecrAlmostLinearSSSP.Decremental.Native.updateReportsPrefix i p B e
                                                  before after (DecrAlmostLinearSSSP.Decremental.scaleCount i))))
                                            (∀ (address : Nat),
                                              @LE.le.{0} Nat instLENat address B →
                                                And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                  (@Eq.{1} Real (t.realMem address) (s.realMem address))))))))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (e : Fin i.k)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine),
  (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
      DecrAlmostLinearSSSP.Decremental.Ends p
        (DecrAlmostLinearSSSP.Decremental.deletionMachine p (before q) (@Fin.val i.k e)) (after q)) →
    ∀ (d : Nat),
      @LE.le.{0} Nat instLENat d (DecrAlmostLinearSSSP.Decremental.scaleCount i) →
        @LE.le.{0} Nat instLENat d (DecrAlmostLinearSSSP.Decremental.Native.updateWorkPrefix i before after d)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Nat
    (DecrAlmostLinearSSSP.Decremental.Native.updateWorkPrefix i before after
      (DecrAlmostLinearSSSP.Decremental.scaleCount i))
    (∑ q, @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (after q).work (before q).work))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B reserve : Nat}
  {machines : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine}
  {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal} {ptr : Fin i.n → Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve machines b ptr s →
    DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve
      (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
      (DecrAlmostLinearSSSP.Decremental.Native.boundaryAdapter i b ptr) (@List.nil.{0} (Fin i.n)) s) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B reserve : Nat}
  {machines : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine}
  {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal} {ptr : Fin i.n → Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve machines b ptr s →
    DecrAlmostLinearSSSP.Decremental.Native.FamilyMemory i p B reserve machines
      (DecrAlmostLinearSSSP.Decremental.Native.boundaryAdapter i b ptr) s) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (ptr : Fin i.n → Nat),
  DecrAlmostLinearSSSP.Decremental.OutputConsistent i (DecrAlmostLinearSSSP.Decremental.Native.boundaryAdapter i b ptr))))) ∧ (((∀ {n : Nat} (l : DecrAlmostLinearSSSP.Decremental.AnswerTable.Layout n) (flagBase listBase : Nat),
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
                                          @Membership.mem.{0, 0} (Fin n) (List.{0} (Fin n))
                                              (@List.instMembership.{0} (Fin n)) xs v →
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
                                              (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B reserve N : Nat),
  @LE.le.{0} Nat instLENat i.n B →
    ∀ (a : DecrAlmostLinearSSSP.Decremental.AdapterState i) (xs : List.{0} (Fin i.n))
      (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
        DecrAlmostLinearSSSP.Decremental.Native.Globals i B
            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                reserve N).utility
            s →
          DecrAlmostLinearSSSP.Decremental.OutputConsistent i a →
            (∀ (v : Fin i.n),
                And
                  (@LE.le.{0} Nat instLENat (s.natMem (@Fin.val i.n v))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Eq.{1} Nat (s.natMem (@Fin.val i.n v))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                    @LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (s.realMem (@Fin.val i.n v)))) →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).pointer →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
                    (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                        (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).flags →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 102) (instOfNatNat (nat_lit 102))))
                      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                          (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).list →
                    ∃ cost t,
                      And
                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                          DecrAlmostLinearSSSP.Decremental.DirtyCommit.code s cost t)
                        (And
                          (@LE.le.{0} Nat instLENat cost
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))
                                (@List.length.{0} (Fin i.n) xs))
                              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                          (And
                            (DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N
                              (DecrAlmostLinearSSSP.Decremental.adapterCommit i a) (@List.nil.{0} (Fin i.n)) t)
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
                                    (DecrAlmostLinearSSSP.Decremental.selected i
                                      (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a)
                                      (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a) v))
                                (DecrAlmostLinearSSSP.Decremental.Native.PublicFrame
                                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N)
                                  i.n s t))))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (e : Fin i.k)
          (before after :
            Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
          (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (ptr : Fin i.n → Nat)
          (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve before b ptr s →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (@Fin.val i.k e) →
              (∀ (v : Fin i.n), DecrAlmostLinearSSSP.Decremental.PointerValid i b v (ptr v)) →
                (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                    DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail
                      (DecrAlmostLinearSSSP.Decremental.registerBound p.code) (before q)) →
                  (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                      DecrAlmostLinearSSSP.Decremental.Ends p
                        (DecrAlmostLinearSSSP.Decremental.deletionMachine p (before q) (@Fin.val i.k e)) (after q)) →
                    (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                        @LE.le.{0} Nat instLENat (after q).work reserve) →
                      (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
                          And
                            (@LE.le.{0} Nat instLENat ((after q).natMem (@Fin.val i.n v))
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (@Eq.{1} Nat ((after q).natMem (@Fin.val i.n v))
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                              @LE.le.{0} Real Real.instLE
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                ((after q).realMem (@Fin.val i.n v)))) →
                        have initial := DecrAlmostLinearSSSP.Decremental.Native.boundaryAdapter i b ptr;
                        have final :=
                          DecrAlmostLinearSSSP.Decremental.adapterTrace i initial
                            (DecrAlmostLinearSSSP.Decremental.Native.updateEventsPrefix i p B e before after
                              (DecrAlmostLinearSSSP.Decremental.scaleCount i));
                        ∃ cost t,
                          And
                            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                              (DecrAlmostLinearSSSP.Decremental.Native.normalUpdate p) s cost t)
                            (And
                              (DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve after
                                (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i final)
                                (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i final) t)
                              (@LE.le.{0} Nat instLENat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                    (DecrAlmostLinearSSSP.Decremental.pointerEnergy i initial)))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (DecrAlmostLinearSSSP.Decremental.Native.scaleUpdateCharge p i.size)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
                                    (DecrAlmostLinearSSSP.Decremental.Native.updateWorkPrefix i before after
                                      (DecrAlmostLinearSSSP.Decremental.scaleCount i)))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                    (DecrAlmostLinearSSSP.Decremental.pointerEnergy i final)))))) ∧ ((∀ (e : Nat),
  DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame
    (DecrAlmostLinearSSSP.Decremental.Structured.natural (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
      e)) ∧ (∀ (e : Nat),
  DecrAlmostLinearSSSP.Decremental.Native.PublicControlFrame
    (DecrAlmostLinearSSSP.Decremental.Structured.natural (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
      e))))))))) := by sorry
