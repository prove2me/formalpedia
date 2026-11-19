-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_4
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:20:07.737449+00:00
-- url     : https://prove2.me/theorems/7f12f781-7523-430f-85a0-63132ed125b3
-- title:
--   Tape translation and saved register records
-- statement:
--   Let a source program be a fixed finite deterministic scalar RAM program. Host states contain natural and real registers and memory; scaled instances, cached observations, advancing pointers and dirty queues are the objects defined by the wrapper interface.
--
--   The tape-copy program translates every source graph record into its shifted memory bank with the prescribed endpoint and weight values. Register-save records preserve the source natural and real register banks and work counter. Address-range and frame contracts identify all memory cells unaffected by these copies.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_4 : (((((((@Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.registersBelow DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code
    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
  Bool.true) ∧ (∀ (j : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) j →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.call
      (DecrAlmostLinearSSSP.Decremental.shadowReg j))) ∧ ((∀ (j : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) j →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.call
      (DecrAlmostLinearSSSP.Decremental.shadowReg j)) ∧ (∀ (N : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N →
    ∀ (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (cost : Nat),
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ScaledCeiling.call s cost t →
        (∀ (j : Nat),
            @LE.le.{0} Nat instLENat N j →
              And
                (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
          ∀ (j : Nat),
            @LE.le.{0} Nat instLENat N j →
              And
                (@Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@Eq.{1} Real (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
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
            (@List.nil.{0} DecrAlmostLinearSSSP.Decremental.Structured.Cmd)))))
    s (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.TapeCopy.finishNatural s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (N : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        @LE.le.{0} Real Real.instLE
            (@Nat.cast.{0} Real Real.instNatCast
              (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              N) →
          ∃ cost t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.TapeCopy.naturalField s
                cost t)
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
                          (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                        (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
                (And
                  (@Eq.{1} Nat (t.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164)))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                      (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162)))))))
                  (And
                    (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (And
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))))))
                      (And
                        (∀ (address : Nat),
                          @Ne.{1} Nat address
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164)))) →
                            (∀ (a : Nat),
                                @Ne.{1} Nat address
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                              And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                (@Eq.{1} Real (t.realMem address) (s.realMem address)))
                        (∀ (address : Nat),
                          (∀ (a : Nat),
                              @Ne.{1} Nat address
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                            @Eq.{1} Real (t.realMem address) (s.realMem address))))))))) ∧ ((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 172) (instOfNatNat (nat_lit 172))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 174) (instOfNatNat (nat_lit 174))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))) →
                DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                  DecrAlmostLinearSSSP.Decremental.TapeCopy.naturalField k) ∧ ((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.naturalField k) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (N : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))) →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202)))) →
          (@LE.le.{0} Real Real.instLE (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202))))
                (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 148) (instOfNatNat (nat_lit 148)))) →
              @LE.le.{0} Real Real.instLE
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202))))
                  (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))))
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  N)) →
            ∃ cost t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.TapeCopy.chooseWeight
                  s cost t)
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
                            (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                          (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                  (And
                    (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 174) (instOfNatNat (nat_lit 174))))
                      (@ite.{1} Nat
                        (@LT.lt.{0} Real Real.instLT
                          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 148) (instOfNatNat (nat_lit 148))))
                          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202)))))
                        ((s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 148) (instOfNatNat (nat_lit 148)))).decidableLT
                          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202)))))
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                          (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                            (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202))))
                              (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))))))))
                    (∀ (address : Nat),
                      (∀ (a : Nat),
                          @Ne.{1} Nat address
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                        And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                          (@Eq.{1} Nat (t.natMem address) (s.natMem address)))))))))) ∧ ((((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 174) (instOfNatNat (nat_lit 174))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.chooseWeight k) ∧ (∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.chooseWeight k)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (N : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))) →
          (@LE.le.{0} Real Real.instLE
                (@Nat.cast.{0} Real Real.instNatCast
                  (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))))
                (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 148) (instOfNatNat (nat_lit 148)))) →
              @LE.le.{0} Real Real.instLE
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@Nat.cast.{0} Real Real.instNatCast
                    (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))))
                  (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))))
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  N)) →
            ∃ cost t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.TapeCopy.weightField
                  s cost t)
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
                            (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                          (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))))
                  (And
                    (@Eq.{1} Nat (t.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164)))))
                      (@ite.{1} Nat
                        (@LT.lt.{0} Real Real.instLT
                          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 148) (instOfNatNat (nat_lit 148))))
                          (@Nat.cast.{0} Real Real.instNatCast
                            (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162)))))))
                        ((s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 148) (instOfNatNat (nat_lit 148)))).decidableLT
                          (@Nat.cast.{0} Real Real.instNatCast
                            (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162)))))))
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                          (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                            (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@Nat.cast.{0} Real Real.instNatCast
                                (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))))
                              (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))))))))
                    (And
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (And
                        (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))))))
                        (And
                          (∀ (address : Nat),
                            @Ne.{1} Nat address
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164)))) →
                              (∀ (a : Nat),
                                  @Ne.{1} Nat address
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                  (@Eq.{1} Real (t.realMem address) (s.realMem address)))
                          (∀ (address : Nat),
                            (∀ (a : Nat),
                                @Ne.{1} Nat address
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                              @Eq.{1} Real (t.realMem address) (s.realMem address)))))))) ∧ (∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 172) (instOfNatNat (nat_lit 172))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 174) (instOfNatNat (nat_lit 174))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))) →
                DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                  DecrAlmostLinearSSSP.Decremental.TapeCopy.weightField k))) ∧ (((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.weightField k) ∧ (∀ {B bank : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {natural : Nat → Nat} {real : Nat → Real},
  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank s natural real →
    (∀ (a : Nat),
        And
          (@Eq.{1} Nat (t.natMem (DecrAlmostLinearSSSP.Decremental.bankAddress B bank a))
            (s.natMem (DecrAlmostLinearSSSP.Decremental.bankAddress B bank a)))
          (@Eq.{1} Real (t.realMem (DecrAlmostLinearSSSP.Decremental.bankAddress B bank a))
            (s.realMem (DecrAlmostLinearSSSP.Decremental.bankAddress B bank a)))) →
      DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank t natural real)) ∧ ((∀ {B bank tail logical value : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {natural : Nat → Nat}
  {real : Nat → Real},
  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank s natural real →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) tail)) →
      @Eq.{1} Nat (t.natMem (DecrAlmostLinearSSSP.Decremental.bankAddress B bank logical))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (DecrAlmostLinearSSSP.Decremental.bankFactor bank) value) →
        (∀ (address : Nat),
            @Ne.{1} Nat address (DecrAlmostLinearSSSP.Decremental.bankAddress B bank logical) →
              (∀ (a : Nat),
                  @Ne.{1} Nat address
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                  (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
          (∀ (address : Nat),
              (∀ (a : Nat),
                  @Ne.{1} Nat address
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                @Eq.{1} Real (t.realMem address) (s.realMem address)) →
            DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank t
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat natural logical value) real) ∧ ((∀ {B bank tail logical : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) tail)) →
    (∀ (address : Nat),
        @Ne.{1} Nat address (DecrAlmostLinearSSSP.Decremental.bankAddress B bank logical) →
          (∀ (a : Nat),
              @Ne.{1} Nat address
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
            And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
              (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
      ∀ (address : Nat),
        @LE.le.{0} Nat instLENat address B →
          And (@Eq.{1} Nat (t.natMem address) (s.natMem address)) (@Eq.{1} Real (t.realMem address) (s.realMem address))) ∧ (∀ {B bank other tail logical : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @Ne.{1} Nat other bank →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) tail)) →
      (∀ (address : Nat),
          @Ne.{1} Nat address (DecrAlmostLinearSSSP.Decremental.bankAddress B bank logical) →
            (∀ (a : Nat),
                @Ne.{1} Nat address
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
              And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
        ∀ (a : Nat),
          And
            (@Eq.{1} Nat (t.natMem (DecrAlmostLinearSSSP.Decremental.bankAddress B other a))
              (s.natMem (DecrAlmostLinearSSSP.Decremental.bankAddress B other a)))
            (@Eq.{1} Real (t.realMem (DecrAlmostLinearSSSP.Decremental.bankAddress B other a))
              (s.realMem (DecrAlmostLinearSSSP.Decremental.bankAddress B other a))))))))) ∧ (((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (N B bank tail logical : Nat) (natural : Nat → Nat)
  (real : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank s natural real →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) tail)) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
          (DecrAlmostLinearSSSP.Decremental.bankAddress B bank logical) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
            (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                @LE.le.{0} Real Real.instLE
                    (@Nat.cast.{0} Real Real.instNatCast
                      (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))))
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                      (@OfNat.ofNat.{0} Real (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      N) →
                  ∃ cost t,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                        DecrAlmostLinearSSSP.Decremental.TapeCopy.naturalField s cost t)
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
                                  (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                                (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
                        (And
                          (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank t
                            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat natural logical
                              (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))))
                            real)
                          (And
                            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                            (And
                              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))))))
                              (And
                                (∀ (address : Nat),
                                  @LE.le.{0} Nat instLENat address B →
                                    And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                      (@Eq.{1} Real (t.realMem address) (s.realMem address)))
                                (∀ (address : Nat),
                                  @Ne.{1} Nat address (DecrAlmostLinearSSSP.Decremental.bankAddress B bank logical) →
                                    (∀ (a : Nat),
                                        @Ne.{1} Nat address
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                      And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                        (@Eq.{1} Real (t.realMem address) (s.realMem address))))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (N B bank tail logical high : Nat) (natural : Nat → Nat)
  (real : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank s natural real →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) tail)) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
          (DecrAlmostLinearSSSP.Decremental.bankAddress B bank logical) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
            (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (DecrAlmostLinearSSSP.Decremental.bankFactor bank) high) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  @LT.lt.{0} Real Real.instLT
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))) →
                    (@LE.le.{0} Real Real.instLE
                          (@Nat.cast.{0} Real Real.instNatCast
                            (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))))
                          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 148) (instOfNatNat (nat_lit 148)))) →
                        @LE.le.{0} Real Real.instLE
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@Nat.cast.{0} Real Real.instNatCast
                              (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))))
                            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))))
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            N)) →
                      ∃ cost t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            DecrAlmostLinearSSSP.Decremental.TapeCopy.weightField s cost t)
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
                                      (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))))
                            (And
                              (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank t
                                (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat natural logical
                                  (@ite.{1} Nat
                                    (@LT.lt.{0} Real Real.instLT
                                      (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 148) (instOfNatNat (nat_lit 148))))
                                      (@Nat.cast.{0} Real Real.instNatCast
                                        (s.natMem
                                          (s.natReg
                                            (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162)))))))
                                    ((s.realReg
                                          (@OfNat.ofNat.{0} Nat (nat_lit 148) (instOfNatNat (nat_lit 148)))).decidableLT
                                      (@Nat.cast.{0} Real Real.instNatCast
                                        (s.natMem
                                          (s.natReg
                                            (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162)))))))
                                    high
                                    (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                                      (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder
                                        Real.instFloorRing)
                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                        (@Nat.cast.{0} Real Real.instNatCast
                                          (s.natMem
                                            (s.natReg
                                              (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))))
                                        (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))))))))
                                real)
                              (And
                                (@Eq.{1} Nat
                                  (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                (And
                                  (@Eq.{1} Nat
                                    (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))))))
                                  (And
                                    (∀ (address : Nat),
                                      @LE.le.{0} Nat instLENat address B →
                                        And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                          (@Eq.{1} Real (t.realMem address) (s.realMem address)))
                                    (∀ (address : Nat),
                                      @Ne.{1} Nat address
                                          (DecrAlmostLinearSSSP.Decremental.bankAddress B bank logical) →
                                        (∀ (a : Nat),
                                            @Ne.{1} Nat address
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (s.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                          And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                            (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))))) ∧ ((∀ {B bank tail high cost : Nat} {delta cutoff : Real} {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.TapeCopy.Env B bank tail high delta cutoff s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
      DecrAlmostLinearSSSP.Decremental.TapeCopy.Stable cmd →
        DecrAlmostLinearSSSP.Decremental.TapeCopy.Env B bank tail high delta cutoff t) ∧ (DecrAlmostLinearSSSP.Decremental.TapeCopy.Stable DecrAlmostLinearSSSP.Decremental.TapeCopy.naturalField))) ∧ (((DecrAlmostLinearSSSP.Decremental.TapeCopy.Stable DecrAlmostLinearSSSP.Decremental.TapeCopy.weightField) ∧ (∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TapeCopy.Stable a →
    DecrAlmostLinearSSSP.Decremental.TapeCopy.Stable b → DecrAlmostLinearSSSP.Decremental.TapeCopy.Stable (a.seq b))) ∧ ((DecrAlmostLinearSSSP.Decremental.TapeCopy.Stable
  (DecrAlmostLinearSSSP.Decremental.Structured.nsub (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166)))
    (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166)))
    (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))) ∧ ((∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.TapeCopy.naturalField s cost t →
    @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166))))
      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166))))) ∧ (∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.TapeCopy.weightField s cost t →
    @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166))))
      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166))))))))) ∧ ((((DecrAlmostLinearSSSP.Decremental.TapeCopy.Stable DecrAlmostLinearSSSP.Decremental.TapeCopy.edge) ∧ (∀ (B bank a : Nat),
  @Eq.{1} Nat
    (DecrAlmostLinearSSSP.Decremental.bankAddress B bank
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (DecrAlmostLinearSSSP.Decremental.bankAddress B bank a)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (DecrAlmostLinearSSSP.Decremental.bankFactor bank))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (N B bank tail logical high : Nat) (delta cutoff : Real)
  (natural : Nat → Nat) (real : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.TapeCopy.Env B bank tail high delta cutoff s →
    DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank s natural real →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
          (DecrAlmostLinearSSSP.Decremental.bankAddress B bank logical) →
        @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            B →
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              delta →
            @LE.le.{0} Real Real.instLE
                (@Nat.cast.{0} Real Real.instNatCast
                  (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))))
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  N) →
              @LE.le.{0} Real Real.instLE
                  (@Nat.cast.{0} Real Real.instNatCast
                    (s.natMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    N) →
                (@LE.le.{0} Real Real.instLE
                      (@Nat.cast.{0} Real Real.instNatCast
                        (s.natMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                      cutoff →
                    @LE.le.{0} Real Real.instLE
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@Nat.cast.{0} Real Real.instNatCast
                          (s.natMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                        delta)
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                        N)) →
                  ∃ cost t,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.TapeCopy.edge s
                        cost t)
                      (And
                        (@LE.le.{0} Nat instLENat cost
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
                                    (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 28) (instOfNatNat (nat_lit 28)))))
                        (And
                          (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank t
                            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                                (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat natural logical
                                  (s.natMem
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (s.natMem
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (DecrAlmostLinearSSSP.Decremental.TapeCopy.roundedWeight delta cutoff high
                                (s.natMem
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                            real)
                          (And
                            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            (And
                              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
                                (DecrAlmostLinearSSSP.Decremental.bankAddress B bank
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              (And
                                (@Eq.{1} Nat
                                  (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166))))
                                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166))))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                (And
                                  (∀ (address : Nat),
                                    @LE.le.{0} Nat instLENat address B →
                                      And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                        (@Eq.{1} Real (t.realMem address) (s.realMem address)))
                                  (∀ (address : Nat),
                                    (∀ (j : Nat),
                                        @LT.lt.{0} Nat instLTNat j
                                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                                          @Ne.{1} Nat address
                                            (DecrAlmostLinearSSSP.Decremental.bankAddress B bank
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                                                j))) →
                                      (∀ (a : Nat),
                                          @Ne.{1} Nat address
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (s.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                        And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                          (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (count N B bank tail origin logical high : Nat)
  (delta cutoff : Real) (raw natural : Nat → Nat) (real : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.TapeCopy.Env B bank tail high delta cutoff s →
    DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank s natural real →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162)))) origin →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
            (DecrAlmostLinearSSSP.Decremental.bankAddress B bank logical) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166)))) count →
            @LE.le.{0} Nat instLENat
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) count))
                B →
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  delta →
                (∀ (address : Nat), @LE.le.{0} Nat instLENat address B → @Eq.{1} Nat (s.natMem address) (raw address)) →
                  (∀ (j : Nat),
                      @LT.lt.{0} Nat instLTNat j count →
                        @LE.le.{0} Real Real.instLE
                          (@Nat.cast.{0} Real Real.instNatCast
                            (raw
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))))
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            N)) →
                    (∀ (j : Nat),
                        @LT.lt.{0} Nat instLTNat j count →
                          @LE.le.{0} Real Real.instLE
                            (@Nat.cast.{0} Real Real.instNatCast
                              (raw
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat
                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                              N)) →
                      (∀ (j : Nat),
                          @LT.lt.{0} Nat instLTNat j count →
                            @LE.le.{0} Real Real.instLE
                                (@Nat.cast.{0} Real Real.instNatCast
                                  (raw
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                                cutoff →
                              @LE.le.{0} Real Real.instLE
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                  (@Nat.cast.{0} Real Real.instNatCast
                                    (raw
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) j))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                                  delta)
                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                  (@instHPow.{0, 0} Real Nat
                                    (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                  N)) →
                        ∃ cost t,
                          And
                            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                              DecrAlmostLinearSSSP.Decremental.TapeCopy.code s cost t)
                            (And
                              (@LE.le.{0} Nat instLENat cost
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) count
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
                                              (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              (And
                                (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank t
                                  (DecrAlmostLinearSSSP.Decremental.TapeCopy.tapeImage raw delta cutoff high count
                                    natural origin logical)
                                  real)
                                (And (DecrAlmostLinearSSSP.Decremental.TapeCopy.Env B bank tail high delta cutoff t)
                                  (And
                                    (@Eq.{1} Nat
                                      (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) origin
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) count)))
                                    (And
                                      (@Eq.{1} Nat
                                        (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
                                        (DecrAlmostLinearSSSP.Decremental.bankAddress B bank
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) count))))
                                      (And
                                        (@Eq.{1} Nat
                                          (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166))))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (And
                                          (∀ (address : Nat),
                                            @LE.le.{0} Nat instLENat address B →
                                              @Eq.{1} Nat (t.natMem address) (raw address))
                                          (∀ (address : Nat),
                                            (∀ (j : Nat),
                                                @LT.lt.{0} Nat instLTNat j
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                      count) →
                                                  @Ne.{1} Nat address
                                                    (DecrAlmostLinearSSSP.Decremental.bankAddress B bank
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        logical j))) →
                                              (∀ (a : Nat),
                                                  @Ne.{1} Nat address
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (s.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 48)
                                                            (instOfNatNat (nat_lit 48))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          a))
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                                And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                  (@Eq.{1} Real (t.realMem address) (s.realMem address))))))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.RecordHeader.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
    (DecrAlmostLinearSSSP.Decremental.RecordHeader.result s))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).natMem
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106)))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 134) (instOfNatNat (nat_lit 134))))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (And
                (@Eq.{1} Real
                  ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).realMem
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106)))))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146))))))
                (And
                  (@Eq.{1} Real
                    ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).realMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
                        (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146)))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfNat.ofNat.{0} Real (nat_lit 128)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126)))))))
                        (@Nat.cast.{0} Real Real.instNatCast
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66))))))))
                  (And
                    (@Eq.{1} Nat
                      ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).natReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
                    (And
                      (@Eq.{1} Real
                        ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).realReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 148) (instOfNatNat (nat_lit 148))))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146))))))
                      (@Eq.{1} Real
                        ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).realReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
                            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 146) (instOfNatNat (nat_lit 146)))))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 128)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126)))))))
                            (@Nat.cast.{0} Real Real.instNatCast
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))))))))))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      ∀ (address : Nat),
        @Ne.{1} Nat address (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106)))) →
          @Ne.{1} Nat address
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
            @Ne.{1} Nat address
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
              @Ne.{1} Nat address
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
                And
                  (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).natMem address)
                    (s.natMem address))
                  (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.RecordHeader.result s).realMem address)
                    (s.realMem address)))) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 216) (instOfNatNat (nat_lit 216))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 212) (instOfNatNat (nat_lit 212))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.RecordHeader.code k) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 148) (instOfNatNat (nat_lit 148))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 210) (instOfNatNat (nat_lit 210))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 212) (instOfNatNat (nat_lit 212))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.RecordHeader.code k) ∧ (∀ (j d : Nat), @Even.{0} Nat instAddNat d → @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.shadowReg j) d))))))) ∧ ((((((∀ {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TailFrame a →
    DecrAlmostLinearSSSP.Decremental.TailFrame b → DecrAlmostLinearSSSP.Decremental.TailFrame (a.seq b)) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.call)) ∧ ((∀ (d p x : Nat),
  @Even.{0} Nat instAddNat d →
    DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productReal d p x)) ∧ (∀ (d p x : Nat),
  @Even.{0} Nat instAddNat d →
    DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productNat d p x)))) ∧ (((∀ (ops : List.{0} (Prod.{0, 0} Nat Nat)),
  (∀ (op : Prod.{0, 0} Nat Nat),
      @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (List.{0} (Prod.{0, 0} Nat Nat))
          (@List.instMembership.{0} (Prod.{0, 0} Nat Nat)) ops op →
        @Even.{0} Nat instAddNat (@Prod.fst.{0, 0} Nat Nat op)) →
    DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.batch ops)) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.ordinary)) ∧ ((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.high) ∧ ((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare) ∧ (∀ (N : Nat), DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.SnapshotFill.code N)))))) ∧ ((((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.writeFields) ∧ (∀ (N : Nat),
  DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.ScaleParameters.initializeSnapshot N))) ∧ ((∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TailFrame cmd →
    ∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost N : Nat},
      DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N →
          (∀ (j : Nat),
              @LE.le.{0} Nat instLENat N j →
                And
                  (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
            ∀ (j : Nat),
              @LE.le.{0} Nat instLENat N j →
                And
                  (@Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Eq.{1} Real (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) ∧ ((∀ (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom),
  DecrAlmostLinearSSSP.Decremental.EvenRegisterWrites a.instruction →
    DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom a)) ∧ (∀ (atoms : List.{0} DecrAlmostLinearSSSP.Decremental.Structured.Atom),
  (∀ (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom),
      @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
          (List.{0} DecrAlmostLinearSSSP.Decremental.Structured.Atom)
          (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Structured.Atom) atoms a →
        DecrAlmostLinearSSSP.Decremental.EvenRegisterWrites a.instruction) →
    DecrAlmostLinearSSSP.Decremental.TailFrame
      (DecrAlmostLinearSSSP.Decremental.Structured.sequence
        (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
          DecrAlmostLinearSSSP.Decremental.Structured.Cmd DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom atoms)))))) ∧ (((∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) {a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TailFrame a →
    DecrAlmostLinearSSSP.Decremental.TailFrame b →
      DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.branch test a b)) ∧ (∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) {body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd},
  DecrAlmostLinearSSSP.Decremental.TailFrame body →
    DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body))) ∧ ((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.RecordHeader.code) ∧ ((∀ (d factor q : Nat),
  @Even.{0} Nat instAddNat d →
    DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.repeatedAdd d factor q)) ∧ (∀ (d factor q : Nat),
  @Even.{0} Nat instAddNat d →
    DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.structuredConstant d factor q))))))) ∧ (((((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.cube) ∧ (∀ (coefficient : Nat),
  DecrAlmostLinearSSSP.Decremental.TailFrame
    (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.polynomialReserve coefficient))) ∧ ((DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.countScales) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.scaleArea))) ∧ (((∀ (stride : Nat), DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.Layout.code stride)) ∧ (∀ (coefficient stride : Nat),
  DecrAlmostLinearSSSP.Decremental.TailFrame (DecrAlmostLinearSSSP.Decremental.Prepass.code coefficient stride))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.Layout.postData s).natReg
      (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))))) ∧ ((∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {stride cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Layout.code stride) s cost t →
    @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.TapeCopy.start s
    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
    (DecrAlmostLinearSSSP.Decremental.TapeCopy.startData s)))))) ∧ ((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (B bank n k : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
          (DecrAlmostLinearSSSP.Decremental.bankFactor bank) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) n →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))) k →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (DecrAlmostLinearSSSP.Decremental.bankFactor bank) n) →
              And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.TapeCopy.startData s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))))
                  n)
                (And
                  (@Eq.{1} Nat
                    ((DecrAlmostLinearSSSP.Decremental.TapeCopy.startData s).natReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))))
                    (DecrAlmostLinearSSSP.Decremental.bankAddress B bank n))
                  (And
                    (@Eq.{1} Nat
                      ((DecrAlmostLinearSSSP.Decremental.TapeCopy.startData s).natReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))))
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (DecrAlmostLinearSSSP.Decremental.bankFactor bank)))
                    (@Eq.{1} Nat
                      ((DecrAlmostLinearSSSP.Decremental.TapeCopy.startData s).natReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166))))
                      k)))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.TapeCopy.startData s).natMem s.natMem)
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.TapeCopy.startData s).realMem s.realMem))) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 162) (instOfNatNat (nat_lit 162))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 164) (instOfNatNat (nat_lit 164))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 170) (instOfNatNat (nat_lit 170))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 166) (instOfNatNat (nat_lit 166))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.start k) ∧ ((∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.start k) ∧ (DecrAlmostLinearSSSP.Decremental.TailFrame DecrAlmostLinearSSSP.Decremental.TapeCopy.start)))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.RegisterSave.saveOne j) s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.RegisterSave.savedOne s j)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoreOne j) s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.RegisterSave.restoredOne s j))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (j : Nat),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.RegisterSave.savedOne s j).natReg
      (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (j k : Nat),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.RegisterSave.savedOne s j).natReg
        (DecrAlmostLinearSSSP.Decremental.shadowReg k))
      (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg k)))
    (@Eq.{1} Real
      ((DecrAlmostLinearSSSP.Decremental.RegisterSave.savedOne s j).realReg
        (DecrAlmostLinearSSSP.Decremental.shadowReg k))
      (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg k)))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (j : Nat),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.RegisterSave.savedOne s j).natMem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
      (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j)))
    (@Eq.{1} Real
      ((DecrAlmostLinearSSSP.Decremental.RegisterSave.savedOne s j).realMem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
      (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))))))))))) := by sorry
