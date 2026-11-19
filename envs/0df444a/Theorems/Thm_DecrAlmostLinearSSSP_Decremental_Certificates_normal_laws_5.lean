-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_5
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:20:00.294451+00:00
-- url     : https://prove2.me/theorems/a67d1ea2-8edd-468f-ae4d-7b89634cd322
-- title:
--   Saved source-state calls and cache copying
-- statement:
--   Let a source program be a fixed finite deterministic scalar RAM program. Host states contain natural and real registers and memory; scaled instances, cached observations, advancing pointers and dirty queues are the objects defined by the wrapper interface.
--
--   Saving, restoring and calling a fixed source program preserve the decoded source machine and the disjoint host state. Copying source output cells initializes the per-scale caches with their finite flags and real values. These contracts charge register snapshots, source simulation and cache-copy instructions explicitly.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_5 : (((((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (j address : Nat),
  @Ne.{1} Nat address
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)) →
    And (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.RegisterSave.savedOne s j).natMem address) (s.natMem address))
      (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.RegisterSave.savedOne s j).realMem address) (s.realMem address))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (j : Nat),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.RegisterSave.restoredOne s j).natReg
      (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (j : Nat),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.RegisterSave.restoredOne s j).natReg
        (DecrAlmostLinearSSSP.Decremental.shadowReg j))
      (s.natMem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))))
    (@Eq.{1} Real
      ((DecrAlmostLinearSSSP.Decremental.RegisterSave.restoredOne s j).realReg
        (DecrAlmostLinearSSSP.Decremental.shadowReg j))
      (s.realMem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (j k : Nat),
  @Ne.{1} Nat k j →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.RegisterSave.restoredOne s j).natReg
          (DecrAlmostLinearSSSP.Decremental.shadowReg k))
        (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg k)))
      (@Eq.{1} Real
        ((DecrAlmostLinearSSSP.Decremental.RegisterSave.restoredOne s j).realReg
          (DecrAlmostLinearSSSP.Decremental.shadowReg k))
        (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg k)))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (j : Nat),
  And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoredOne s j).natMem s.natMem)
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoredOne s j).realMem s.realMem)) ∧ (∀ (registers : List.{0} Nat),
  @List.Nodup.{0} Nat registers →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      ∃ t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
            (DecrAlmostLinearSSSP.Decremental.RegisterSave.saveRegisters registers) s
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@List.length.{0} Nat registers))
            t)
          (And
            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))
            (And
              (∀ (k : Nat),
                And
                  (@Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg k))
                    (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg k)))
                  (@Eq.{1} Real (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg k))
                    (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg k))))
              (And
                (∀ (k : Nat),
                  @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) registers k →
                    And
                      (@Eq.{1} Nat
                        (t.natMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)))
                        (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg k)))
                      (@Eq.{1} Real
                        (t.realMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)))
                        (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg k))))
                (∀ (address : Nat),
                  (∀ (k : Nat),
                      @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) registers k →
                        @Ne.{1} Nat address
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))) →
                    And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                      (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))) ∧ ((∀ (registers : List.{0} Nat),
  @List.Nodup.{0} Nat registers →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      ∃ t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
            (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreRegisters registers) s
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@List.length.{0} Nat registers))
            t)
          (And
            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))
            (And (@Eq.{1} (Nat → Nat) t.natMem s.natMem)
              (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                (And
                  (∀ (k : Nat),
                    @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) registers k →
                      And
                        (@Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg k))
                          (s.natMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))))
                        (@Eq.{1} Real (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg k))
                          (s.realMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k)))))
                  (∀ k ∉ registers,
                    And
                      (@Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg k))
                        (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg k)))
                      (@Eq.{1} Real (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg k))
                        (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg k))))))))) ∧ ((∀ (j k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreOne j) k) ∧ (∀ (j k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreOne j) k))))) ∧ ((((∀ (registers : List.{0} Nat) (k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreRegisters registers) k) ∧ (∀ (registers : List.{0} Nat) (k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
      (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreRegisters registers) k)) ∧ ((∀ (B F N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (g : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) g.pc →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) g.work →
      @Eq.{1} Bool
          (@BEq.beq.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          g.halted →
        @Eq.{1} Bool
            (@BEq.beq.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            g.fault →
          (∀ (a : Nat),
              @Eq.{1} Real
                (s.realMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                (g.realMem a)) →
            (∀ (a : Nat),
                @Eq.{1} Nat
                  (s.natMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F (g.natMem a))) →
              (∀ (j : Nat),
                  @LT.lt.{0} Nat instLTNat j N →
                    And
                      (@Eq.{1} Nat
                        (s.natMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F (g.natReg j)))
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
                    ∃ t,
                      And
                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                          (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreRegisters (List.range N)) s
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N)
                          t)
                        (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F t g)) ∧ (∀ (entry : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.SourceSetup.header entry) s
    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
    (DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s)))) ∧ (((∀ (entry : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).realMem s.realMem)
    (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).natMem s.natMem)) ∧ (∀ (entry j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.SourceSetup.header entry)
    (DecrAlmostLinearSSSP.Decremental.shadowReg j))) ∧ ((∀ (entry j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.SourceSetup.header entry)
    (DecrAlmostLinearSSSP.Decremental.shadowReg j)) ∧ ((∀ (entry B F : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))) F →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            B)
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                entry)
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (And
                  (@Eq.{1} Nat
                    ((DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).natReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (And
                    (@Eq.{1} Nat
                      ((DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).natReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                      F)
                    (And
                      (@Eq.{1} Real
                        ((DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).realReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                        (@Nat.cast.{0} Real Real.instNatCast F))
                      (And
                        (@Eq.{1} Nat
                          ((DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).natReg
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (s.natMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
                        (@Eq.{1} Nat
                          ((DecrAlmostLinearSSSP.Decremental.SourceSetup.headerData entry s).natReg
                            (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))))))))))) ∧ (∀ (registers : List.{0} Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NoMemory
    (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreRegisters registers))))))) ∧ (((((∀ (N entry B F : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (g : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))) F →
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
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (g.realMem a)) →
                  (∀ (a : Nat),
                      @Eq.{1} Nat
                        (s.natMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F (g.natMem a))) →
                    (∀ (j : Nat),
                        @LT.lt.{0} Nat instLTNat j N →
                          And
                            (@Eq.{1} Nat
                              (s.natMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F (g.natReg j)))
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
                          ∃ t,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                (DecrAlmostLinearSSSP.Decremental.SourceSetup.code N entry) s
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N))
                                t)
                              (And (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F t g)
                                (And
                                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                    B)
                                  (And
                                    (@Eq.{1} Nat
                                      (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (And
                                      (@Eq.{1} Nat
                                        (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F)
                                      (And
                                        (@Eq.{1} Real
                                          (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                          (@Nat.cast.{0} Real Real.instNatCast F))
                                        (And
                                          (@Eq.{1} Nat
                                            (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                          (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                                            (@Eq.{1} (Nat → Nat) t.natMem s.natMem))))))))) ∧ (∀ {B bank start : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (DecrAlmostLinearSSSP.Decremental.bankFactor bank) s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
            (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
              (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.bankFactor bank)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
              ∀ (reports : List.{0} Nat),
                DecrAlmostLinearSSSP.Decremental.ReportLog start reports s →
                  (∃ r,
                      @Eq.{1} Nat start
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                    ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
                      ∃ cost t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            (DecrAlmostLinearSSSP.Decremental.observedInstruction g.pc ins) s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (DecrAlmostLinearSSSP.Decremental.actionBound ins)
                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                            (And
                              (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                                (DecrAlmostLinearSSSP.Decremental.bankFactor bank) t
                                (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                                  {
                                    pc :=
                                      @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                                    realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
                                    halted := g.halted, fault := g.fault,
                                    work :=
                                      @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }))
                              (DecrAlmostLinearSSSP.Decremental.ReportLog start
                                (@HAppend.hAppend.{0, 0, 0} (List.{0} Nat) (List.{0} Nat) (List.{0} Nat)
                                  (@instHAppendOfAppend.{0} (List.{0} Nat) (@List.instAppend.{0} Nat)) reports
                                  (DecrAlmostLinearSSSP.Decremental.physicalWrites B bank ins g))
                                t))))) ∧ ((∀ {B bank start : Nat} (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (g : DecrAlmostLinearSSSP.Decremental.Machine),
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (DecrAlmostLinearSSSP.Decremental.bankFactor bank) s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
            (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
              (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.bankFactor bank)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
              ∀ (reports : List.{0} Nat),
                DecrAlmostLinearSSSP.Decremental.ReportLog start reports s →
                  (∃ r,
                      @Eq.{1} Nat start
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                    @LE.le.{0} Nat instLENat pc g.pc →
                      ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
                        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                              DecrAlmostLinearSSSP.Decremental.Instruction
                              (fun as i =>
                                @LT.lt.{0} Nat instLTNat i
                                  (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) g.pc pc))
                            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
                          ∃ cost t,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                (DecrAlmostLinearSSSP.Decremental.observedDispatchAux pc code) s cost t)
                              (And
                                (@LE.le.{0} Nat instLENat cost
                                  (DecrAlmostLinearSSSP.Decremental.observedDispatchCharge code))
                                (And
                                  (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                                    (DecrAlmostLinearSSSP.Decremental.bankFactor bank) t
                                    (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                                      {
                                        pc :=
                                          @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                                        realReg := g.realReg, natReg := g.natReg, realMem := g.realMem,
                                        natMem := g.natMem, halted := g.halted, fault := g.fault,
                                        work :=
                                          @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }))
                                  (DecrAlmostLinearSSSP.Decremental.ReportLog start
                                    (@HAppend.hAppend.{0, 0, 0} (List.{0} Nat) (List.{0} Nat) (List.{0} Nat)
                                      (@instHAppendOfAppend.{0} (List.{0} Nat) (@List.instAppend.{0} Nat)) reports
                                      (DecrAlmostLinearSSSP.Decremental.physicalWrites B bank ins g))
                                    t)))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) k →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.appendStoreReport k))) ∧ (((∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.appendStoreReport k) ∧ (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k →
      @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) k →
        @Ne.{1} Nat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) k →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.observedAction ins) k)) ∧ ((∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.observedAction ins) k) ∧ ((∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  DecrAlmostLinearSSSP.Decremental.Structured.FlagFrame (DecrAlmostLinearSSSP.Decremental.observedAction ins)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) ∧ (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.observedAction ins)
    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))) ∧ ((((∀ (pc : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.observedInstruction pc ins) k) ∧ (∀ (pc : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.observedInstruction pc ins)
    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) ∧ ((∀ (pc : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  DecrAlmostLinearSSSP.Decremental.Structured.FlagFrame (DecrAlmostLinearSSSP.Decremental.observedInstruction pc ins)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) ∧ ((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (start k : Nat),
  Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.observedDispatchAux start code) k) ∧ (∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (start : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.observedDispatchAux start code)
    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))) ∧ (((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (start : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.FlagFrame
    (DecrAlmostLinearSSSP.Decremental.observedDispatchAux start code)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) ∧ (∀ (pc : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.observedInstruction pc ins)
    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))) ∧ ((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.observedDispatchAux pc code)
    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))) ∧ ((∀ (j k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.RegisterSave.saveOne j) k) ∧ (∀ (registers : List.{0} Nat) (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
        (DecrAlmostLinearSSSP.Decremental.RegisterSave.saveRegisters registers) k))))))) ∧ ((((((∀ (j k : Nat),
  @Even.{0} Nat instAddNat k →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
          (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreOne j) k) ∧ (∀ (registers : List.{0} Nat) (k : Nat),
  @Even.{0} Nat instAddNat k →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
          (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreRegisters registers) k)) ∧ ((∀ (registers : List.{0} Nat) (k : Nat),
  @Even.{0} Nat instAddNat k →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
      (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreRegisters registers) k) ∧ (∀ (N entry k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            (DecrAlmostLinearSSSP.Decremental.SourceSetup.code N entry) k))) ∧ (((∀ (N entry k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.SourceSetup.code N entry)
        k) ∧ (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.observedAction ins) k)) ∧ ((∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @Even.{0} Nat instAddNat k →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.observedAction ins) k) ∧ ((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
        (DecrAlmostLinearSSSP.Decremental.observedDispatchAux pc code) k) ∧ (∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc k : Nat),
  @Even.{0} Nat instAddNat k →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.observedDispatchAux pc code)
      k))))) ∧ ((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.SourceSnapshot.workCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.SourceSnapshot.workData s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.SourceSnapshot.workData s).natMem
    (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.SourceSnapshot.workData s).realMem s.realMem) ∧ ((∀ (N k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.SourceSnapshot.code N) k) ∧ (∀ (N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
    ∃ t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.SourceSnapshot.code N) s
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          t)
        (And
          (@Eq.{1} Nat
            (t.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
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
                    (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j)))
                  (@Eq.{1} Real
                    (t.realMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                    (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))))
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
                    (@Eq.{1} Real (t.realMem address) (s.realMem address))))))))) ∧ (((∀ (B bank record a : Nat),
  (∃ r,
      @Eq.{1} Nat record
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    And
      (@Ne.{1} Nat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
      (∀ (j : Nat),
        @Ne.{1} Nat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))) ∧ (∀ (N k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.SourceSnapshot.code N) k)) ∧ ((∀ (N entry : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            (DecrAlmostLinearSSSP.Decremental.SourceCall.code N entry p) k) ∧ ((∀ (N entry : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.SourceCall.code N entry p)
        k) ∧ (∀ (N entry B bank : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
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
                                ∃ cost t,
                                  And
                                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                      (DecrAlmostLinearSSSP.Decremental.SourceCall.code N entry p) s cost t)
                                    (And
                                      (@LE.le.{0} Nat instLENat cost
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (DecrAlmostLinearSSSP.Decremental.dispatchCharge p.code)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                                final.work g.work))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))
                                      (And
                                        (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                                          (DecrAlmostLinearSSSP.Decremental.bankFactor bank) t final)
                                        (And
                                          (@Eq.{1} Nat
                                            (t.natMem
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (s.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                                            final.work)
                                          (And
                                            (∀ (j : Nat),
                                              @LT.lt.{0} Nat instLTNat j N →
                                                And
                                                  (@Eq.{1} Nat
                                                    (t.natMem
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (s.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 50)
                                                            (instOfNatNat (nat_lit 50))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          j)))
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                      (final.natReg j)))
                                                  (@Eq.{1} Real
                                                    (t.realMem
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (s.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 50)
                                                            (instOfNatNat (nat_lit 50))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          j)))
                                                    (final.realReg j)))
                                            (∀ (address : Nat),
                                              (∀ (a : Nat),
                                                  @Ne.{1} Nat address
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))
                                                            a)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))))) →
                                                @Ne.{1} Nat address
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (s.natReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 106)
                                                          (instOfNatNat (nat_lit 106))))
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
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
                                                    And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                      (@Eq.{1} Real (t.realMem address) (s.realMem address))))))))))))) ∧ (((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @LE.le.{0} Nat instLENat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @LE.le.{0} Nat instLENat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        (@Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))) →
          (@Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))) →
            ∃ cost t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ExtendedMax.code s
                  cost t)
                (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                  (And
                    (@LE.le.{0} Nat instLENat
                      (t.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (And
                      (@Eq.{1} Nat (t.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                        @LE.le.{0} Real Real.instLE
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                          (t.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))))
                      (And
                        (@Eq.{1} ENNReal
                          (DecrAlmostLinearSSSP.Decremental.ExtendedMax.cell t
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                          (@Max.max.{0} ENNReal ENNReal.instMax
                            (DecrAlmostLinearSSSP.Decremental.ExtendedMax.cell s
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                            (DecrAlmostLinearSSSP.Decremental.ExtendedMax.incoming s)))
                        (∀ (address : Nat),
                          @Ne.{1} Nat address
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))) →
                            And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                              (@Eq.{1} Nat (t.natMem address) (s.natMem address)))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (F flag : Nat) (delta r : Real),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132)))) F →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))) delta →
          @LE.le.{0} Nat instLENat flag (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
            @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128)))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F flag) →
              @Eq.{1} Real (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))))) r →
                (@Eq.{1} Nat flag (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                    @LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r) →
                  ∃ cost t,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                        DecrAlmostLinearSSSP.Decremental.ScaledReadout.code s cost t)
                      (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                        (And
                          (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))) flag)
                          (And
                            (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) delta r))
                            (And
                              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                                @LE.le.{0} Real Real.instLE
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                  (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                              (And
                                (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.ExtendedMax.incoming t)
                                  (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                                    (@instHMul.{0} ENNReal
                                      (@Distrib.toMul.{0} ENNReal
                                        (@instDistribOfSemiring.{0} ENNReal
                                          (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                                    (ENNReal.ofReal delta)
                                    (@ite.{1} ENNReal
                                      (@Eq.{1} Nat flag (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (instDecidableEqNat flag
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (@Top.top.{0} ENNReal ENNReal.instTop) (ENNReal.ofReal r))))
                                (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                                  (@Eq.{1} (Nat → Nat) t.natMem s.natMem))))))))) ∧ ((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.ScaledReadout.code) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CacheCopy.suffix s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.CacheCopy.suffixData s)))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 130) (instOfNatNat (nat_lit 130))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.ScaledReadout.code k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.ScaledReadout.code k)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (F flag : Nat) (delta r : Real),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132)))) F →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))) delta →
          @LE.le.{0} Nat instLENat flag (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
            @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128)))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F flag) →
              @Eq.{1} Real (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))))) r →
                (@Eq.{1} Nat flag (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                    @LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                      ∃ cost t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            DecrAlmostLinearSSSP.Decremental.CacheCopy.body s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
                            (And
                              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              (And
                                (@Eq.{1} Nat
                                  (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))))
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))))
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))))))
                                (And
                                  (@Eq.{1} Nat
                                    (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176))))
                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176))))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (And
                                    (@Eq.{1} Nat
                                      (t.natMem
                                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                                      flag)
                                    (And
                                      (@Eq.{1} Real
                                        (t.realMem
                                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
                                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) delta r))
                                      (∀ (address : Nat),
                                        @Ne.{1} Nat address
                                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))) →
                                          And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                            (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))))) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 130) (instOfNatNat (nat_lit 130))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176))) →
            DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.body k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.body k))))) ∧ ((((∀ (count sourceBase cacheBase stride F : Nat) (delta : Real) (flags : Nat → Nat) (values : Nat → Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132)))) F →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))) delta →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128)))) sourceBase →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))) cacheBase →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170)))) stride →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176)))) count →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                        (∀ (j : Nat),
                            @LT.lt.{0} Nat instLTNat j count →
                              @LE.le.{0} Nat instLENat (flags j)
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                          (∀ (j : Nat),
                              @LT.lt.{0} Nat instLTNat j count →
                                @Eq.{1} Nat (flags j) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                                  @LE.le.{0} Real Real.instLE
                                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                    (values j)) →
                            (∀ (j : Nat),
                                @LT.lt.{0} Nat instLTNat j count →
                                  @Eq.{1} Nat
                                    (s.natMem
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) sourceBase
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride j)))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F (flags j))) →
                              (∀ (j : Nat),
                                  @LT.lt.{0} Nat instLTNat j count →
                                    @Eq.{1} Real
                                      (s.realMem
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) sourceBase
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride j)))
                                      (values j)) →
                                (∀ (j : Nat),
                                    @LT.lt.{0} Nat instLTNat j count →
                                      ∀ (k : Nat),
                                        @LT.lt.{0} Nat instLTNat k count →
                                          @Ne.{1} Nat
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) sourceBase
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride
                                                j))
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cacheBase
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) k))) →
                                  ∃ cost t,
                                    And
                                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                        DecrAlmostLinearSSSP.Decremental.CacheCopy.code s cost t)
                                      (And
                                        (@LE.le.{0} Nat instLENat cost
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) count)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                        (And
                                          (@Eq.{1} Nat
                                            (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))))
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) sourceBase
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride
                                                count)))
                                          (And
                                            (@Eq.{1} Nat
                                              (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cacheBase
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) count)))
                                            (And
                                              (@Eq.{1} Nat
                                                (t.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176))))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                              (And
                                                (∀ (j : Nat),
                                                  @LT.lt.{0} Nat instLTNat j count →
                                                    And
                                                      (@Eq.{1} Nat
                                                        (t.natMem
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) cacheBase
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              j)))
                                                        (flags j))
                                                      (@Eq.{1} Real
                                                        (t.realMem
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) cacheBase
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              j)))
                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul) delta (values j))))
                                                (∀ (address : Nat),
                                                  (∀ (j : Nat),
                                                      @LT.lt.{0} Nat instLTNat j count →
                                                        @Ne.{1} Nat address
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) cacheBase
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              j))) →
                                                    And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                      (@Eq.{1} Real (t.realMem address) (s.realMem address))))))))) ∧ (∀ (B bank cacheOffset count : Nat) (delta : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (g : DecrAlmostLinearSSSP.Decremental.Machine),
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (DecrAlmostLinearSSSP.Decremental.bankFactor bank) s g →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132))))
          (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))) delta →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (DecrAlmostLinearSSSP.Decremental.bankFactor bank)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) cacheOffset))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (DecrAlmostLinearSSSP.Decremental.bankFactor bank)) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176)))) count →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                        (∀ (v : Fin count),
                            @LE.le.{0} Nat instLENat (g.natMem (@Fin.val count v))
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                          (∀ (v : Fin count),
                              @Eq.{1} Nat (g.natMem (@Fin.val count v))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                                @LE.le.{0} Real Real.instLE
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                  (g.realMem (@Fin.val count v))) →
                            ∃ cost t,
                              And
                                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                  DecrAlmostLinearSSSP.Decremental.CacheCopy.code s cost t)
                                (And
                                  (@LE.le.{0} Nat instLENat cost
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) count)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                  (And
                                    (∀ (v : Fin count),
                                      And
                                        (@Eq.{1} Nat
                                          (t.natMem
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    cacheOffset))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                (@Fin.val count v))))
                                          (g.natMem (@Fin.val count v)))
                                        (And
                                          (@Eq.{1} Real
                                            (t.realMem
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      cacheOffset))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  (@Fin.val count v))))
                                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) delta
                                              (g.realMem (@Fin.val count v))))
                                          (@Eq.{1} ENNReal
                                            (DecrAlmostLinearSSSP.Decremental.ExtendedMax.cell t
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      cacheOffset))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  (@Fin.val count v))))
                                            (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                                              (@instHMul.{0} ENNReal
                                                (@Distrib.toMul.{0} ENNReal
                                                  (@instDistribOfSemiring.{0} ENNReal
                                                    (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                                              (ENNReal.ofReal delta)
                                              (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val count v))))))
                                    (And
                                      (∀ (address : Nat),
                                        (∀ (j : Nat),
                                            @LT.lt.{0} Nat instLTNat j count →
                                              @Ne.{1} Nat address
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                        cacheOffset))
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))) →
                                          And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                            (@Eq.{1} Real (t.realMem address) (s.realMem address)))
                                      (∀ (a : Nat),
                                        And
                                          (@Eq.{1} Nat
                                            (t.natMem
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                                            (s.natMem
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
                                          (@Eq.{1} Real
                                            (t.realMem
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                                            (s.realMem
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                      (instOfNatNat (nat_lit 1)))))))))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CacheCopy.setup s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.CacheCopy.setupData s)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CacheCopy.setupData s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.CacheCopy.setupData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.CacheCopy.setupData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.CacheCopy.setupData s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108)))))
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.CacheCopy.setupData s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66))))))))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176))) →
            DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.setup k)))) ∧ (((∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.setup k) ∧ (∀ (B bank cacheOffset count : Nat) (delta : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (g : DecrAlmostLinearSSSP.Decremental.Machine),
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (DecrAlmostLinearSSSP.Decremental.bankFactor bank) s g →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) delta →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
            (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) cacheOffset))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) count →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))) delta →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                      (∀ (v : Fin count),
                          @LE.le.{0} Nat instLENat (g.natMem (@Fin.val count v))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                        (∀ (v : Fin count),
                            @Eq.{1} Nat (g.natMem (@Fin.val count v))
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                              @LE.le.{0} Real Real.instLE
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                (g.realMem (@Fin.val count v))) →
                          ∃ cost t,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                DecrAlmostLinearSSSP.Decremental.CacheCopy.call s cost t)
                              (And
                                (@LE.le.{0} Nat instLENat cost
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) count)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                (And
                                  (∀ (v : Fin count),
                                    And
                                      (@Eq.{1} Nat
                                        (t.natMem
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  cacheOffset))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              (@Fin.val count v))))
                                        (g.natMem (@Fin.val count v)))
                                      (And
                                        (@Eq.{1} Real
                                          (t.realMem
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    cacheOffset))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                (@Fin.val count v))))
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) delta
                                            (g.realMem (@Fin.val count v))))
                                        (@Eq.{1} ENNReal
                                          (DecrAlmostLinearSSSP.Decremental.ExtendedMax.cell t
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    cacheOffset))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                (@Fin.val count v))))
                                          (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                                            (@instHMul.{0} ENNReal
                                              (@Distrib.toMul.{0} ENNReal
                                                (@instDistribOfSemiring.{0} ENNReal
                                                  (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                                            (ENNReal.ofReal delta)
                                            (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val count v))))))
                                  (And
                                    (∀ (address : Nat),
                                      (∀ (j : Nat),
                                          @LT.lt.{0} Nat instLTNat j count →
                                            @Ne.{1} Nat address
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      cacheOffset))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))) →
                                        And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                          (@Eq.{1} Real (t.realMem address) (s.realMem address)))
                                    (∀ (a : Nat),
                                      And
                                        (@Eq.{1} Nat
                                          (t.natMem
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                                          (s.natMem
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
                                        (@Eq.{1} Real
                                          (t.realMem
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                                          (s.realMem
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))))) ∧ ((∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame b →
      DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame (a.seq b)) ∧ ((∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) {body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame body →
    DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body)) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B utility cost : Nat}
  {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame cmd →
        DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility t)))))))) := by sorry
