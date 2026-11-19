-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_6
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_6
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:21:15.441117+00:00
-- url     : https://prove2.me/theorems/b5dc3331-f1e9-4e72-954a-98edd0d6949f
-- title:
--   Global frames and initial scale records
-- statement:
--   Let a source program be a fixed finite deterministic scalar RAM program. Host states contain natural and real registers and memory; scaled instances, cached observations, advancing pointers and dirty queues are the objects defined by the wrapper interface.
--
--   Global parameters and per-scale metadata remain stable across initialization subroutines. Native record construction writes the source pointer, cache pointers, work fields and saved-register region for each scale. A loop over the scales establishes the corresponding initialized memory images and preserves the original input tape.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_6 : (((((((DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.RecordHeader.code) ∧ (∀ (N : Nat), DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame (DecrAlmostLinearSSSP.Decremental.SnapshotFill.code N))) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare) ∧ (DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.writeFields))) ∧ (((∀ (N : Nat),
  DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame
    (DecrAlmostLinearSSSP.Decremental.ScaleParameters.initializeSnapshot N)) ∧ (DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.start)) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.naturalField) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.weightField) ∧ (DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.edge))))) ∧ ((((DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.code) ∧ (∀ (N entry : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame (DecrAlmostLinearSSSP.Decremental.SourceCall.code N entry p))) ∧ ((∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {coefficient stride cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Prepass.code coefficient stride) s
      cost t →
    @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))))) ∧ (∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {i : DecrAlmostLinearSSSP.Decremental.Input}
  {coefficient stride cost : Nat},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Prepass.code coefficient stride)
        s cost t →
      DecrAlmostLinearSSSP.Decremental.Layout.Represents t
          (DecrAlmostLinearSSSP.Decremental.Layout.addresses
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) coefficient
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) i.size
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            stride) →
        DecrAlmostLinearSSSP.Decremental.Native.Globals i
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (DecrAlmostLinearSSSP.Decremental.Layout.addresses
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) coefficient
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) i.size
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              stride).utility
          t))) ∧ (((∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.BankFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.BankFrame b → DecrAlmostLinearSSSP.Decremental.Native.BankFrame (a.seq b)) ∧ (∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) {body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.BankFrame body →
    DecrAlmostLinearSSSP.Decremental.Native.BankFrame (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body))) ∧ ((∀ {j record cache stride cost : Nat} {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.BankEnv j record cache stride s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
      DecrAlmostLinearSSSP.Decremental.Native.BankFrame cmd →
        DecrAlmostLinearSSSP.Decremental.Native.BankEnv j record cache stride t) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.BankFrame DecrAlmostLinearSSSP.Decremental.RecordHeader.code) ∧ (∀ (N : Nat), DecrAlmostLinearSSSP.Decremental.Native.BankFrame (DecrAlmostLinearSSSP.Decremental.SnapshotFill.code N))))))) ∧ (((((DecrAlmostLinearSSSP.Decremental.Native.BankFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare) ∧ (DecrAlmostLinearSSSP.Decremental.Native.BankFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.writeFields)) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.BankFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.start) ∧ (DecrAlmostLinearSSSP.Decremental.Native.BankFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.naturalField))) ∧ (((DecrAlmostLinearSSSP.Decremental.Native.BankFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.weightField) ∧ (∀ (N entry : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Native.BankFrame (DecrAlmostLinearSSSP.Decremental.SourceCall.code N entry p))) ∧ ((∀ (N : Nat),
  DecrAlmostLinearSSSP.Decremental.Native.BankFrame
    (DecrAlmostLinearSSSP.Decremental.ScaleParameters.initializeSnapshot N)) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.BankFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.edge) ∧ (DecrAlmostLinearSSSP.Decremental.Native.BankFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.code))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (j B utility record cache stride N : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility s →
    DecrAlmostLinearSSSP.Decremental.Native.BankEnv j record cache stride s →
      (∃ r,
          @Eq.{1} Nat record
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N →
          (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j s
              (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun x =>
              @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
            ∀ (raw : Nat → Nat),
              (∀ (address : Nat), @LE.le.{0} Nat instLENat address B → @Eq.{1} Nat (s.natMem address) (raw address)) →
                (∀ (r : Nat),
                    @LE.le.{0} Nat instLENat N r →
                      And
                        (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                  ∃ t,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                        DecrAlmostLinearSSSP.Decremental.RecordHeader.code s
                        (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19))) t)
                      (And (DecrAlmostLinearSSSP.Decremental.Native.Ready i j B utility record cache stride t)
                        (And
                          (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j t
                            (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun x =>
                            @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                          (And
                            (∀ (address : Nat),
                              @LE.le.{0} Nat instLENat address B → @Eq.{1} Nat (t.natMem address) (raw address))
                            (And
                              (∀ (r : Nat),
                                @LE.le.{0} Nat instLENat N r →
                                  And
                                    (@Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                    (@Eq.{1} Real (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                              (∀ (address : Nat),
                                @Ne.{1} Nat address record →
                                  @Ne.{1} Nat address
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                                    @Ne.{1} Nat address
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
                                      @Ne.{1} Nat address
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                                            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
                                        And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                          (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))) ∧ (∀ (N k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 204) (instOfNatNat (nat_lit 204))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 208) (instOfNatNat (nat_lit 208))) →
                  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
                    (DecrAlmostLinearSSSP.Decremental.ScaleParameters.initializeSnapshot N) k)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program),
      @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@Nat.cast.{0} Real Real.instNatCast i.size))
          i.accuracy →
        ∀ (j B utility record cache stride N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          DecrAlmostLinearSSSP.Decremental.Native.Ready i j B utility record cache stride s →
            @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N →
              (∃ r,
                  @Eq.{1} Nat record
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                (∃ u,
                    @Eq.{1} Nat utility
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) u))) →
                  (∀ (r : Nat),
                      @LT.lt.{0} Nat instLTNat r N →
                        @LT.lt.{0} Nat instLTNat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                          utility) →
                    (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j s
                        (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun x =>
                        @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                      ∀ (raw : Nat → Nat),
                        (∀ (address : Nat),
                            @LE.le.{0} Nat instLENat address B → @Eq.{1} Nat (s.natMem address) (raw address)) →
                          (∀ (r : Nat),
                              @LE.le.{0} Nat instLENat N r →
                                And
                                  (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                  (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                            ∃ cost t,
                              And
                                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                  (DecrAlmostLinearSSSP.Decremental.ScaleParameters.initializeSnapshot N) s cost t)
                                (And
                                  (@LE.le.{0} Nat instLENat cost
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) N)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                                DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                                (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 109) (instOfNatNat (nat_lit 109)))))
                                  (And
                                    (DecrAlmostLinearSSSP.Decremental.Native.Ready i j B utility record cache stride t)
                                    (And
                                      (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j t
                                        (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun x =>
                                        @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                                      (And
                                        (@Eq.{1} Nat
                                          (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))))
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (DecrAlmostLinearSSSP.Decremental.bankFactor j) i.n))
                                        (And
                                          (@Eq.{1} Nat
                                            (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (DecrAlmostLinearSSSP.Decremental.bankFactor j)
                                              (DecrAlmostLinearSSSP.Decremental.barrierHigh i)))
                                          (And
                                            (∀ (r : Nat),
                                              @LT.lt.{0} Nat instLTNat r N →
                                                And
                                                  (@Eq.{1} Nat
                                                    (t.natMem
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          record
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          r)))
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (DecrAlmostLinearSSSP.Decremental.bankFactor j)
                                                      ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                            (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).natReg
                                                        r)))
                                                  (@Eq.{1} Real
                                                    (t.realMem
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          record
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          r)))
                                                    ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                          (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).realReg
                                                      r)))
                                            (And
                                              (∀ (address : Nat),
                                                @LE.le.{0} Nat instLENat address B →
                                                  @Eq.{1} Nat (t.natMem address) (raw address))
                                              (And
                                                (∀ (r : Nat),
                                                  @LE.le.{0} Nat instLENat N r →
                                                    And
                                                      (@Eq.{1} Nat
                                                        (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                      (@Eq.{1} Real
                                                        (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                                        (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                          (@Zero.toOfNat0.{0} Real Real.instZero))))
                                                (∀ (address : Nat),
                                                  (∀ (r : Nat),
                                                      @LT.lt.{0} Nat instLTNat r N →
                                                        @Ne.{1} Nat address
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) record
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 8)
                                                                (instOfNatNat (nat_lit 8))))
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              r))) →
                                                    (∀ (a : Nat),
                                                        @Ne.{1} Nat address
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) utility
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                a))
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                              (instOfNatNat (nat_lit 1))))) →
                                                      And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                        (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))))))) ∧ ((∀ (raw : Nat → Nat) (delta cutoff : Real) (high : Nat) (natural : Nat → Nat) (origin logical address : Nat),
  @Ne.{1} Nat address logical →
    @Ne.{1} Nat address
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      @Ne.{1} Nat address
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        @Eq.{1} Nat
          (DecrAlmostLinearSSSP.Decremental.TapeCopy.edgeImage raw delta cutoff high natural origin logical address)
          (natural address)) ∧ (∀ (raw : Nat → Nat) (delta cutoff : Real) (high count : Nat) (natural : Nat → Nat) (origin logical address : Nat),
  Or (@LT.lt.{0} Nat instLTNat address logical)
      (@LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) count))
        address) →
    @Eq.{1} Nat
      (DecrAlmostLinearSSSP.Decremental.TapeCopy.tapeImage raw delta cutoff high count natural origin logical address)
      (natural address))))) ∧ (((∀ (raw : Nat → Nat) (delta cutoff : Real) (high count : Nat) (natural : Nat → Nat) (origin logical j : Nat),
  @LT.lt.{0} Nat instLTNat j count →
    And
      (@Eq.{1} Nat
        (DecrAlmostLinearSSSP.Decremental.TapeCopy.tapeImage raw delta cutoff high count natural origin logical
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j)))
        (raw
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))))
      (And
        (@Eq.{1} Nat
          (DecrAlmostLinearSSSP.Decremental.TapeCopy.tapeImage raw delta cutoff high count natural origin logical
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (raw
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@Eq.{1} Nat
          (DecrAlmostLinearSSSP.Decremental.TapeCopy.tapeImage raw delta cutoff high count natural origin logical
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (DecrAlmostLinearSSSP.Decremental.TapeCopy.roundedWeight delta cutoff high
            (raw
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (j : Nat) (e : Fin i.k),
  @Eq.{1} Nat
    (DecrAlmostLinearSSSP.Decremental.TapeCopy.roundedWeight (DecrAlmostLinearSSSP.Decremental.delta i j)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (DecrAlmostLinearSSSP.Decremental.scale j))
      (DecrAlmostLinearSSSP.Decremental.barrierHigh i) (i.weight e))
    (DecrAlmostLinearSSSP.Decremental.barrierWeight i j e))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input) (j : Nat),
  @Eq.{1} (Nat → Nat)
    (DecrAlmostLinearSSSP.Decremental.TapeCopy.tapeImage (DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem
      (DecrAlmostLinearSSSP.Decremental.delta i j)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (DecrAlmostLinearSSSP.Decremental.scale j))
      (DecrAlmostLinearSSSP.Decremental.barrierHigh i) i.k
      (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) i.n i.n)
    (DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).natMem) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (x : Nat),
      @LE.le.{0} Nat instLENat x i.size →
        @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast x)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LT.lt.{0} Real Real.instLT
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@Nat.cast.{0} Real Real.instNatCast i.size))
        i.accuracy →
      ∀ (j : Nat) (w : Real),
        @LE.le.{0} Real Real.instLE w
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (DecrAlmostLinearSSSP.Decremental.scale j)) →
          @LE.le.{0} Real Real.instLE
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) w
              (DecrAlmostLinearSSSP.Decremental.delta i j))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))))))))) ∧ ((((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LT.lt.{0} Real Real.instLT
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@Nat.cast.{0} Real Real.instNatCast i.size))
        i.accuracy →
      ∀ (j B bank tail : Nat),
        DecrAlmostLinearSSSP.Decremental.TapeCopy.Env B bank tail (DecrAlmostLinearSSSP.Decremental.barrierHigh i)
            (DecrAlmostLinearSSSP.Decremental.delta i j)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (DecrAlmostLinearSSSP.Decremental.scale j))
            s →
          (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank s
              (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun x =>
              @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162)))) i.n →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
                  (DecrAlmostLinearSSSP.Decremental.bankAddress B bank i.n) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166)))) i.k →
                  @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                      B →
                    (∀ (address : Nat),
                        @LE.le.{0} Nat instLENat address B →
                          @Eq.{1} Nat (s.natMem address)
                            ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem address)) →
                      ∃ cost t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            DecrAlmostLinearSSSP.Decremental.TapeCopy.code s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.k
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                            DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                            (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (And
                              (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank t
                                (DecrAlmostLinearSSSP.Decremental.initialMachine p
                                    (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).natMem
                                (DecrAlmostLinearSSSP.Decremental.initialMachine p
                                    (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).realMem)
                              (And
                                (DecrAlmostLinearSSSP.Decremental.TapeCopy.Env B bank tail
                                  (DecrAlmostLinearSSSP.Decremental.barrierHigh i)
                                  (DecrAlmostLinearSSSP.Decremental.delta i j)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                    (DecrAlmostLinearSSSP.Decremental.scale j))
                                  t)
                                (And
                                  (@Eq.{1} Nat
                                    (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k)))
                                  (And
                                    (@Eq.{1} Nat
                                      (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
                                      (DecrAlmostLinearSSSP.Decremental.bankAddress B bank
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))))
                                    (And
                                      (@Eq.{1} Nat
                                        (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166))))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                      (And
                                        (∀ (address : Nat),
                                          @LE.le.{0} Nat instLENat address B →
                                            @Eq.{1} Nat (t.natMem address)
                                              ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem address))
                                        (∀ (address : Nat),
                                          (∀ (a : Nat),
                                              @LT.lt.{0} Nat instLTNat a
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k) →
                                                @Ne.{1} Nat address
                                                  (DecrAlmostLinearSSSP.Decremental.bankAddress B bank
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                                      a))) →
                                            (∀ (a : Nat),
                                                @Ne.{1} Nat address
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (s.natReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                        a))
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                              And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                (@Eq.{1} Real (t.realMem address) (s.realMem address))))))))))) ∧ (∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame a →
    DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame b →
      DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame (a.seq b))) ∧ ((DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.start) ∧ (DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.naturalField))) ∧ (((DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.weightField) ∧ (DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.edge)) ∧ ((DecrAlmostLinearSSSP.Decremental.TapeCopy.ConstantFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.code) ∧ ((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.Structured.Cmd.skip) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame
  (DecrAlmostLinearSSSP.Decremental.Structured.sequence
    (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Structured.Cmd
      (DecrAlmostLinearSSSP.Decremental.Structured.storeN
        (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164)))
        (@OfNat.ofNat.{0} Nat (nat_lit 174) (instOfNatNat (nat_lit 174))))
      (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        (DecrAlmostLinearSSSP.Decremental.Structured.nadd
          (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162)))
          (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162)))
          (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Structured.Cmd
          (DecrAlmostLinearSSSP.Decremental.Structured.nadd
            (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164)))
            (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164)))
            (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))))
          (@List.nil.{0} DecrAlmostLinearSSSP.Decremental.Structured.Cmd)))))))))) ∧ ((((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.naturalField) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.chooseWeight)) ∧ ((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.weightField) ∧ ((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.edge) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.code)))) ∧ (((∀ (B bank record offset : Nat),
  (∃ r,
      @Eq.{1} Nat record
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    @Even.{0} Nat instAddNat offset →
      ∀ (a : Nat),
        @Ne.{1} Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record offset)
          (DecrAlmostLinearSSSP.Decremental.bankAddress B bank a)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program),
      @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@Nat.cast.{0} Real Real.instNatCast i.size))
          i.accuracy →
        ∀ (j B utility record cache stride N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          DecrAlmostLinearSSSP.Decremental.Native.Ready i j B utility record cache stride s →
            @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N →
              (∃ r,
                  @Eq.{1} Nat record
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                (∃ u,
                    @Eq.{1} Nat utility
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) u))) →
                  (∀ (r : Nat),
                      @LT.lt.{0} Nat instLTNat r N →
                        @LT.lt.{0} Nat instLTNat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                          utility) →
                    @LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                        B →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (DecrAlmostLinearSSSP.Decremental.bankFactor j) i.n) →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (DecrAlmostLinearSSSP.Decremental.bankFactor j)
                              (DecrAlmostLinearSSSP.Decremental.barrierHigh i)) →
                          (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j s
                              (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun x =>
                              @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                            (∀ (r : Nat),
                                @LT.lt.{0} Nat instLTNat r N →
                                  And
                                    (@Eq.{1} Nat
                                      (s.natMem
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                                            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (DecrAlmostLinearSSSP.Decremental.bankFactor j)
                                        ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                              (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).natReg
                                          r)))
                                    (@Eq.{1} Real
                                      (s.realMem
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                                            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)))
                                      ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                            (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).realReg
                                        r))) →
                              (∀ (address : Nat),
                                  @LE.le.{0} Nat instLENat address B →
                                    @Eq.{1} Nat (s.natMem address)
                                      ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem address)) →
                                (∀ (r : Nat),
                                    @LE.le.{0} Nat instLENat N r →
                                      And
                                        (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                          (@OfNat.ofNat.{0} Real (nat_lit 0)
                                            (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                                  ∃ cost t,
                                    And
                                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                        DecrAlmostLinearSSSP.Decremental.Native.prepareTape s cost t)
                                      (And
                                        (@LE.le.{0} Nat instLENat cost
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.k
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                                        DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                                        (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
                                        (And
                                          (DecrAlmostLinearSSSP.Decremental.Native.Ready i j B utility record cache
                                            stride t)
                                          (And
                                            (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j t
                                              (DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                  (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).natMem
                                              (DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                  (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).realMem)
                                            (And
                                              (∀ (r : Nat),
                                                @LT.lt.{0} Nat instLTNat r N →
                                                  And
                                                    (@Eq.{1} Nat
                                                      (t.natMem
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) record
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 8)
                                                              (instOfNatNat (nat_lit 8))))
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))
                                                            r)))
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (DecrAlmostLinearSSSP.Decremental.bankFactor j)
                                                        ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                              (DecrAlmostLinearSSSP.Decremental.barrierInput i
                                                                j)).natReg
                                                          r)))
                                                    (@Eq.{1} Real
                                                      (t.realMem
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) record
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 8)
                                                              (instOfNatNat (nat_lit 8))))
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))
                                                            r)))
                                                      ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                            (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).realReg
                                                        r)))
                                              (And
                                                (∀ (address : Nat),
                                                  @LE.le.{0} Nat instLENat address B →
                                                    @Eq.{1} Nat (t.natMem address)
                                                      ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem
                                                        address))
                                                (And
                                                  (∀ (r : Nat),
                                                    @LE.le.{0} Nat instLENat N r →
                                                      And
                                                        (@Eq.{1} Nat
                                                          (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                        (@Eq.{1} Real
                                                          (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                                          (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                            (@Zero.toOfNat0.{0} Real Real.instZero))))
                                                  (∀ (address : Nat),
                                                    (∀ (a : Nat),
                                                        @LT.lt.{0} Nat instLTNat a
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                (instOfNatNat (nat_lit 3)))
                                                              i.k) →
                                                          @Ne.{1} Nat address
                                                            (DecrAlmostLinearSSSP.Decremental.bankAddress B j
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) i.n a))) →
                                                      (∀ (a : Nat),
                                                          @Ne.{1} Nat address
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) utility
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                    (instOfNatNat (nat_lit 2)))
                                                                  a))
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1))))) →
                                                        And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                          (@Eq.{1} Real (t.realMem address) (s.realMem address))))))))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {j record cache next : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next s →
    (∀ (offset : Nat),
        @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
            (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (@List.nil.{0} Nat))))
            offset →
          And
            (@Eq.{1} Nat (t.natMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record offset))
              (s.natMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record offset)))
            (@Eq.{1} Real (t.realMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record offset))
              (s.realMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record offset)))) →
      DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next t) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {j B utility record cache stride cost : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility s →
    DecrAlmostLinearSSSP.Decremental.Native.BankEnv j record cache stride s →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.RecordHeader.code s cost t →
        DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record stride) t) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {j record cache next utility N : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next s →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N →
      (∀ (r : Nat),
          @LT.lt.{0} Nat instLTNat r N →
            @LT.lt.{0} Nat instLTNat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
              utility) →
        (∀ (address : Nat),
            (∀ (r : Nat),
                @LT.lt.{0} Nat instLTNat r N →
                  @Ne.{1} Nat address
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))) →
              (∀ (a : Nat),
                  @Ne.{1} Nat address
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) utility
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                  (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
          DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next t)))))) ∧ (((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {j B record cache next utility N : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next s →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N →
      (∃ r,
          @Eq.{1} Nat record
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
        (∀ (r : Nat),
            @LT.lt.{0} Nat instLTNat r N →
              @LT.lt.{0} Nat instLTNat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                utility) →
          (∀ (address : Nat),
              (∀ (a : Nat),
                  @LT.lt.{0} Nat instLTNat a
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k) →
                    @Ne.{1} Nat address
                      (DecrAlmostLinearSSSP.Decremental.bankAddress B j
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n a))) →
                (∀ (a : Nat),
                    @Ne.{1} Nat address
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) utility
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                  And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                    (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
            DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next t) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program),
      @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@Nat.cast.{0} Real Real.instNatCast i.size))
          i.accuracy →
        ∀ (j B utility record cache stride N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility s →
            DecrAlmostLinearSSSP.Decremental.Native.BankEnv j record cache stride s →
              @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N →
                (∃ r,
                    @Eq.{1} Nat record
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                  (∃ u,
                      @Eq.{1} Nat utility
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) u))) →
                    (∀ (r : Nat),
                        @LT.lt.{0} Nat instLTNat r N →
                          @LT.lt.{0} Nat instLTNat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                            utility) →
                      @LE.le.{0} Nat instLENat
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                          B →
                        (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j s
                            (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun x =>
                            @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                          (∀ (address : Nat),
                              @LE.le.{0} Nat instLENat address B →
                                @Eq.{1} Nat (s.natMem address)
                                  ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem address)) →
                            (∀ (r : Nat),
                                @LE.le.{0} Nat instLENat N r →
                                  And
                                    (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                    (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                              ∃ cost t,
                                And
                                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                    (DecrAlmostLinearSSSP.Decremental.Native.prepareBank N) s cost t)
                                  (And
                                    (@LE.le.{0} Nat instLENat cost
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) N)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                                    DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                                    (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))))
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.k
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                                      DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                                      (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 136) (instOfNatNat (nat_lit 136)))))
                                    (And
                                      (DecrAlmostLinearSSSP.Decremental.Native.Ready i j B utility record cache stride
                                        t)
                                      (And
                                        (DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                                            stride)
                                          t)
                                        (And
                                          (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j t
                                            (DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).natMem
                                            (DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).realMem)
                                          (And
                                            (∀ (r : Nat),
                                              @LT.lt.{0} Nat instLTNat r N →
                                                And
                                                  (@Eq.{1} Nat
                                                    (t.natMem
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          record
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          r)))
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (DecrAlmostLinearSSSP.Decremental.bankFactor j)
                                                      ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                            (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).natReg
                                                        r)))
                                                  (@Eq.{1} Real
                                                    (t.realMem
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          record
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          r)))
                                                    ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                          (DecrAlmostLinearSSSP.Decremental.barrierInput i j)).realReg
                                                      r)))
                                            (And
                                              (∀ (address : Nat),
                                                @LE.le.{0} Nat instLENat address B →
                                                  @Eq.{1} Nat (t.natMem address)
                                                    ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem
                                                      address))
                                              (And
                                                (∀ (r : Nat),
                                                  @LE.le.{0} Nat instLENat N r →
                                                    And
                                                      (@Eq.{1} Nat
                                                        (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                      (@Eq.{1} Real
                                                        (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                                        (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                          (@Zero.toOfNat0.{0} Real Real.instZero))))
                                                (∀ (address : Nat),
                                                  (∀ (r : Nat),
                                                      @LT.lt.{0} Nat instLTNat r
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) N
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))) →
                                                        @Ne.{1} Nat address
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat) record
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              r))) →
                                                    (∀ (v : Nat),
                                                        @LT.lt.{0} Nat instLTNat v
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                                (instOfNatNat (nat_lit 3)))
                                                              i.k) →
                                                          @Ne.{1} Nat address
                                                            (DecrAlmostLinearSSSP.Decremental.bankAddress B j
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) i.n v))) →
                                                      (∀ (a : Nat),
                                                          @Ne.{1} Nat address
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) utility
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                    (instOfNatNat (nat_lit 2)))
                                                                  a))
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                (instOfNatNat (nat_lit 1))))) →
                                                        And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                          (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))))))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (queryBound : Nat)
  (i : DecrAlmostLinearSSSP.Decremental.Input),
  DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false i →
    ∀ (B bank : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
            (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @Eq.{1} Nat
                (s.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              (∀ (addr : Nat),
                  @Eq.{1} Real
                    (s.realMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) addr)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                    ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).realMem addr)) →
                (∀ (addr : Nat),
                    @Eq.{1} Nat
                      (s.natMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) addr)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                        ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem addr))) →
                  (∀ (j : Nat),
                      @LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.registerBound p.code) →
                        And
                          (@Eq.{1} Nat
                            (s.natMem
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                              ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natReg j)))
                          (@Eq.{1} Real
                            (s.realMem
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                            ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).realReg j))) →
                    (∀ (j : Nat),
                        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code) j →
                          And
                            (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                            (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
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
                          ∃ final cost t,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Ends p
                                (DecrAlmostLinearSSSP.Decremental.initialMachine p i) final)
                              (And
                                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                  (DecrAlmostLinearSSSP.Decremental.SourceCall.code
                                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code) p.initPC p)
                                  s cost t)
                                (And
                                  (@LE.le.{0} Nat instLENat cost
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (DecrAlmostLinearSSSP.Decremental.dispatchCharge p.code)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          final.work)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                                          (DecrAlmostLinearSSSP.Decremental.registerBound p.code)))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))
                                  (And
                                    (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                                      (DecrAlmostLinearSSSP.Decremental.bankFactor bank) t final)
                                    (And
                                      (DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail
                                        (DecrAlmostLinearSSSP.Decremental.registerBound p.code) final)
                                      (And
                                        (@Eq.{1} ENNReal
                                          (DecrAlmostLinearSSSP.Decremental.stored final (@Fin.val i.n i.source))
                                          (@OfNat.ofNat.{0} ENNReal (nat_lit 0)
                                            (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
                                        (And
                                          (∀ (v : Fin i.n),
                                            And
                                              (@LE.le.{0} Nat instLENat (final.natMem (@Fin.val i.n v))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                              (@Eq.{1} Nat (final.natMem (@Fin.val i.n v))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                                                @LE.le.{0} Real Real.instLE
                                                  (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                    (@Zero.toOfNat0.{0} Real Real.instZero))
                                                  (final.realMem (@Fin.val i.n v))))
                                          (And
                                            (∀ (v : Fin i.n),
                                              And
                                                (@LE.le.{0} ENNReal ENNReal.instLE (i.dist (@List.nil.{0} (Fin i.k)) v)
                                                  (DecrAlmostLinearSSSP.Decremental.stored final (@Fin.val i.n v)))
                                                (And
                                                  (@LE.le.{0} ENNReal ENNReal.instLE
                                                    (DecrAlmostLinearSSSP.Decremental.stored final (@Fin.val i.n v))
                                                    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                                                      (@instHMul.{0} ENNReal
                                                        (@Distrib.toMul.{0} ENNReal
                                                          (@instDistribOfSemiring.{0} ENNReal
                                                            (@CommSemiring.toSemiring.{0} ENNReal
                                                              ENNReal.instCommSemiring))))
                                                      (ENNReal.ofReal
                                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                          (@instHAdd.{0} Real Real.instAdd)
                                                          (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                            (@One.toOfNat1.{0} Real Real.instOne))
                                                          i.accuracy))
                                                      (i.dist (@List.nil.{0} (Fin i.k)) v)))
                                                  (Iff
                                                    (@Eq.{1} ENNReal
                                                      (DecrAlmostLinearSSSP.Decremental.stored final (@Fin.val i.n v))
                                                      (@Top.top.{0} ENNReal ENNReal.instTop))
                                                    (Not
                                                      (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph
                                                        (@DecrAlmostLinearSSSP.Decremental.live i.k
                                                          (@List.nil.{0} (Fin i.k)))
                                                        i.source v)))))
                                            (And
                                              (@LE.le.{0} Real Real.instLE
                                                (@Nat.cast.{0} Real Real.instNatCast final.work)
                                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                  (@instHDiv.{0} Real
                                                    (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul) C
                                                      (@Nat.cast.{0} Real Real.instNatCast i.size))
                                                    (a i.size))
                                                  i.accuracy))
                                              (And
                                                (@Eq.{1} Nat
                                                  (t.natMem
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (s.natReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 106)
                                                          (instOfNatNat (nat_lit 106))))
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                                                  final.work)
                                                (And
                                                  (∀ (j : Nat),
                                                    @LT.lt.{0} Nat instLTNat j
                                                        (DecrAlmostLinearSSSP.Decremental.registerBound p.code) →
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
                                                    (∀ (addr : Nat),
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
                                                                  addr)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1))))))) →
                                                      @Ne.{1} Nat address
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (s.natReg
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 106)
                                                                (instOfNatNat (nat_lit 106))))
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 6)
                                                              (instOfNatNat (nat_lit 6)))) →
                                                        (∀ (j : Nat),
                                                            @LT.lt.{0} Nat instLTNat j
                                                                (DecrAlmostLinearSSSP.Decremental.registerBound
                                                                  p.code) →
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
                                                            (@Eq.{1} Real (t.realMem address)
                                                              (s.realMem address)))))))))))))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 130) (instOfNatNat (nat_lit 130))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 176) (instOfNatNat (nat_lit 176))) →
                DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.call k))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.call k) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.call)) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.call) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.BankFrame DecrAlmostLinearSSSP.Decremental.CacheCopy.call) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {j B record cache next N : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next s →
    (∃ r,
        @Eq.{1} Nat record
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      (∀ (address : Nat),
          (∀ (a : Nat),
              @Ne.{1} Nat address
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (DecrAlmostLinearSSSP.Decremental.bankFactor j)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
            @Ne.{1} Nat address
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
              (∀ (r : Nat),
                  @LT.lt.{0} Nat instLTNat r N →
                    @Ne.{1} Nat address
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))) →
                And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                  (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
        DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next t))))) ∧ ((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {j record cache next count : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next s →
    @LT.lt.{0} Nat instLTNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
        cache →
      (∀ (address : Nat),
          (∀ (v : Nat),
              @LT.lt.{0} Nat instLTNat v count →
                @Ne.{1} Nat address
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cache
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v))) →
            And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
              (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
        DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next t) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (queryBound : Nat),
      @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@Nat.cast.{0} Real Real.instNatCast i.size))
          i.accuracy →
        ∀ (j B utility record cache stride : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false
              (DecrAlmostLinearSSSP.Decremental.barrierInput i j) →
            DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility s →
              DecrAlmostLinearSSSP.Decremental.Native.BankEnv j record cache stride s →
                (∃ r,
                    @Eq.{1} Nat record
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                  (∃ c,
                      @Eq.{1} Nat cache
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) c))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                    (∃ u,
                        @Eq.{1} Nat utility
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) u))) →
                      (∀ (r : Nat),
                          @LT.lt.{0} Nat instLTNat r (DecrAlmostLinearSSSP.Decremental.registerBound p.code) →
                            @LT.lt.{0} Nat instLTNat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
                              utility) →
                        @LT.lt.{0} Nat instLTNat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            cache →
                          @LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                              B →
                            (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j s
                                (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun x =>
                                @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                              (∀ (address : Nat),
                                  @LE.le.{0} Nat instLENat address B →
                                    @Eq.{1} Nat (s.natMem address)
                                      ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem address)) →
                                (∀ (r : Nat),
                                    @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code) r →
                                      And
                                        (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg r))
                                          (@OfNat.ofNat.{0} Real (nat_lit 0)
                                            (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                                  ∃ final cost t,
                                    And
                                      (DecrAlmostLinearSSSP.Decremental.Ends p
                                        (DecrAlmostLinearSSSP.Decremental.initialMachine p
                                          (DecrAlmostLinearSSSP.Decremental.barrierInput i j))
                                        final)
                                      (And
                                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                          (DecrAlmostLinearSSSP.Decremental.Native.initializeScale p) s cost t)
                                        (And
                                          (@LE.le.{0} Nat instLENat cost
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (DecrAlmostLinearSSSP.Decremental.dispatchCharge p.code)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                        final.work)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))
                                                        (DecrAlmostLinearSSSP.Decremental.registerBound p.code)))
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                                            DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 16)
                                                              (instOfNatNat (nat_lit 16)))
                                                            (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 32)
                                                            (instOfNatNat (nat_lit 32)))))))
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.k
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                                              DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                              (instOfNatNat (nat_lit 3))))
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 16)
                                                                (instOfNatNat (nat_lit 16)))
                                                              (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 32)
                                                              (instOfNatNat (nat_lit 32))))))
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))))
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) i.n))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 158) (instOfNatNat (nat_lit 158)))))
                                          (And (DecrAlmostLinearSSSP.Decremental.Native.Globals i B utility t)
                                            (And
                                              (DecrAlmostLinearSSSP.Decremental.Native.BankEnv j record cache stride t)
                                              (And
                                                (DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    record stride)
                                                  t)
                                                (And
                                                  (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B j t
                                                    final.natMem final.realMem)
                                                  (And
                                                    (@Eq.{1} Nat
                                                      (t.natMem
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          record
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 6)
                                                            (instOfNatNat (nat_lit 6)))))
                                                      final.work)
                                                    (And
                                                      (∀ (r : Nat),
                                                        @LT.lt.{0} Nat instLTNat r
                                                            (DecrAlmostLinearSSSP.Decremental.registerBound p.code) →
                                                          And
                                                            (@Eq.{1} Nat
                                                              (t.natMem
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) record
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 8)
                                                                      (instOfNatNat (nat_lit 8))))
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                      (instOfNatNat (nat_lit 2)))
                                                                    r)))
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (DecrAlmostLinearSSSP.Decremental.bankFactor j)
                                                                (final.natReg r)))
                                                            (@Eq.{1} Real
                                                              (t.realMem
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) record
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 8)
                                                                      (instOfNatNat (nat_lit 8))))
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                      (instOfNatNat (nat_lit 2)))
                                                                    r)))
                                                              (final.realReg r)))
                                                      (And
                                                        (∀ (v : Fin i.n),
                                                          And
                                                            (@Eq.{1} Nat
                                                              (t.natMem
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat) cache
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                      (instOfNatNat (nat_lit 2)))
                                                                    (@Fin.val i.n v))))
                                                              (final.natMem (@Fin.val i.n v)))
                                                            (And
                                                              (@Eq.{1} Real
                                                                (t.realMem
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) cache
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat)
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                        (instOfNatNat (nat_lit 2)))
                                                                      (@Fin.val i.n v))))
                                                                (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                  (@instHMul.{0} Real Real.instMul)
                                                                  (DecrAlmostLinearSSSP.Decremental.delta i j)
                                                                  (final.realMem (@Fin.val i.n v))))
                                                              (@Eq.{1} ENNReal
                                                                (DecrAlmostLinearSSSP.Decremental.ExtendedMax.cell t
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat) cache
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat)
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                        (instOfNatNat (nat_lit 2)))
                                                                      (@Fin.val i.n v))))
                                                                (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                                                                  (@instHMul.{0} ENNReal
                                                                    (@Distrib.toMul.{0} ENNReal
                                                                      (@instDistribOfSemiring.{0} ENNReal
                                                                        (@CommSemiring.toSemiring.{0} ENNReal
                                                                          ENNReal.instCommSemiring))))
                                                                  (ENNReal.ofReal
                                                                    (DecrAlmostLinearSSSP.Decremental.delta i j))
                                                                  (DecrAlmostLinearSSSP.Decremental.stored final
                                                                    (@Fin.val i.n v))))))
                                                        (And
                                                          (∀ (v : Fin i.n),
                                                            And
                                                              (@LE.le.{0} Nat instLENat (final.natMem (@Fin.val i.n v))
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                  (instOfNatNat (nat_lit 1))))
                                                              (@Eq.{1} Nat (final.natMem (@Fin.val i.n v))
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                    (instOfNatNat (nat_lit 0))) →
                                                                @LE.le.{0} Real Real.instLE
                                                                  (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                                    (@Zero.toOfNat0.{0} Real Real.instZero))
                                                                  (final.realMem (@Fin.val i.n v))))
                                                          (And
                                                            (∀ (v : Fin i.n),
                                                              And
                                                                (@LE.le.{0} ENNReal ENNReal.instLE
                                                                  ((DecrAlmostLinearSSSP.Decremental.barrierInput i
                                                                        j).dist
                                                                    (@List.nil.{0}
                                                                      (Fin
                                                                        (DecrAlmostLinearSSSP.Decremental.barrierInput i
                                                                            j).k))
                                                                    v)
                                                                  (DecrAlmostLinearSSSP.Decremental.stored final
                                                                    (@Fin.val i.n v)))
                                                                (And
                                                                  (@LE.le.{0} ENNReal ENNReal.instLE
                                                                    (DecrAlmostLinearSSSP.Decremental.stored final
                                                                      (@Fin.val i.n v))
                                                                    (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                                                                      (@instHMul.{0} ENNReal
                                                                        (@Distrib.toMul.{0} ENNReal
                                                                          (@instDistribOfSemiring.{0} ENNReal
                                                                            (@CommSemiring.toSemiring.{0} ENNReal
                                                                              ENNReal.instCommSemiring))))
                                                                      (ENNReal.ofReal
                                                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                                          (@instHAdd.{0} Real Real.instAdd)
                                                                          (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                                            (@One.toOfNat1.{0} Real Real.instOne))
                                                                          (DecrAlmostLinearSSSP.Decremental.barrierInput
                                                                              i j).accuracy))
                                                                      ((DecrAlmostLinearSSSP.Decremental.barrierInput i
                                                                            j).dist
                                                                        (@List.nil.{0}
                                                                          (Fin
                                                                            (DecrAlmostLinearSSSP.Decremental.barrierInput
                                                                                i j).k))
                                                                        v)))
                                                                  (Iff
                                                                    (@Eq.{1} ENNReal
                                                                      (DecrAlmostLinearSSSP.Decremental.stored final
                                                                        (@Fin.val i.n v))
                                                                      (@Top.top.{0} ENNReal ENNReal.instTop))
                                                                    (Not
                                                                      (@DecrAlmostLinearSSSP.Decremental.Reachable i.n
                                                                        i.k i.graph
                                                                        (@DecrAlmostLinearSSSP.Decremental.live i.k
                                                                          (@List.nil.{0} (Fin i.k)))
                                                                        i.source v)))))
                                                            (And
                                                              (@LE.le.{0} Real Real.instLE
                                                                (@Nat.cast.{0} Real Real.instNatCast final.work)
                                                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                                  (@instHDiv.{0} Real
                                                                    (@DivInvMonoid.toDiv.{0} Real
                                                                      Real.instDivInvMonoid))
                                                                  (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                    (@instHMul.{0} Real Real.instMul)
                                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                                      (@instHMul.{0} Real Real.instMul) C
                                                                      (@Nat.cast.{0} Real Real.instNatCast
                                                                        (DecrAlmostLinearSSSP.Decremental.barrierInput i
                                                                            j).size))
                                                                    (a
                                                                      (DecrAlmostLinearSSSP.Decremental.barrierInput i
                                                                          j).size))
                                                                  (DecrAlmostLinearSSSP.Decremental.barrierInput i
                                                                      j).accuracy))
                                                              (And
                                                                (∀ (r : Nat),
                                                                  @LE.le.{0} Nat instLENat
                                                                      (DecrAlmostLinearSSSP.Decremental.registerBound
                                                                        p.code)
                                                                      r →
                                                                    And
                                                                      (@Eq.{1} Nat
                                                                        (t.natReg
                                                                          (DecrAlmostLinearSSSP.Decremental.shadowReg
                                                                            r))
                                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0)
                                                                          (instOfNatNat (nat_lit 0))))
                                                                      (@Eq.{1} Real
                                                                        (t.realReg
                                                                          (DecrAlmostLinearSSSP.Decremental.shadowReg
                                                                            r))
                                                                        (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                                          (@Zero.toOfNat0.{0} Real Real.instZero))))
                                                                (∀ (address : Nat),
                                                                  (∀ (r : Nat),
                                                                      @LT.lt.{0} Nat instLTNat r
                                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                            (@instHAdd.{0} Nat instAddNat)
                                                                            (DecrAlmostLinearSSSP.Decremental.registerBound
                                                                              p.code)
                                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                              (instOfNatNat (nat_lit 4)))) →
                                                                        @Ne.{1} Nat address
                                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                            (@instHAdd.{0} Nat instAddNat) record
                                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                              (@instHMul.{0} Nat instMulNat)
                                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                                (instOfNatNat (nat_lit 2)))
                                                                              r))) →
                                                                    (∀ (v : Nat),
                                                                        @Ne.{1} Nat address
                                                                          (DecrAlmostLinearSSSP.Decremental.bankAddress
                                                                            B j v)) →
                                                                      (∀ (v : Nat),
                                                                          @LT.lt.{0} Nat instLTNat v i.n →
                                                                            @Ne.{1} Nat address
                                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                                (@instHAdd.{0} Nat instAddNat) cache
                                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                                  (@instHMul.{0} Nat instMulNat)
                                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                                    (instOfNatNat (nat_lit 2)))
                                                                                  v))) →
                                                                        (∀ (v : Nat),
                                                                            @Ne.{1} Nat address
                                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                                (@instHAdd.{0} Nat instAddNat)
                                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                                  (@instHAdd.{0} Nat instAddNat) utility
                                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                                    (@instHMul.{0} Nat instMulNat)
                                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                                      (instOfNatNat (nat_lit 2)))
                                                                                    v))
                                                                                (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                                                  (instOfNatNat (nat_lit 1))))) →
                                                                          And
                                                                            (@Eq.{1} Nat (t.natMem address)
                                                                              (s.natMem address))
                                                                            (@Eq.{1} Real (t.realMem address)
                                                                              (s.realMem address)))))))))))))))))) ∧ ((∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.Native.ControlFrame a →
    DecrAlmostLinearSSSP.Decremental.Native.ControlFrame b →
      DecrAlmostLinearSSSP.Decremental.Native.ControlFrame (a.seq b)) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.ControlFrame DecrAlmostLinearSSSP.Decremental.RecordHeader.code) ∧ (∀ (N : Nat), DecrAlmostLinearSSSP.Decremental.Native.ControlFrame (DecrAlmostLinearSSSP.Decremental.SnapshotFill.code N))))) ∧ (((DecrAlmostLinearSSSP.Decremental.Native.ControlFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare) ∧ (DecrAlmostLinearSSSP.Decremental.Native.ControlFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.writeFields)) ∧ ((∀ (N : Nat),
  DecrAlmostLinearSSSP.Decremental.Native.ControlFrame
    (DecrAlmostLinearSSSP.Decremental.ScaleParameters.initializeSnapshot N)) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.ControlFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.start) ∧ (DecrAlmostLinearSSSP.Decremental.Native.ControlFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.naturalField)))))))) := by sorry
