-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_11
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:20:22.181375+00:00
-- url     : https://prove2.me/theorems/233275e4-a9c7-4c90-87a1-63e4a98c0208
-- title:
--   Observed stores and deletion forwarding
-- statement:
--   Let a source program be a fixed finite deterministic scalar RAM program. Host states contain natural and real registers and memory; scaled instances, cached observations, advancing pointers and dirty queues are the objects defined by the wrapper interface.
--
--   Observed source calls record the actual emitted store events and preserve the decoded source execution. Native report consumption updates caches, advances pointers and adds dirty vertices in the same order as the mathematical adapter trace. The deletion header forwards the current identifier while preserving all previously established source and public state.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_11 : (((((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat} {a : DecrAlmostLinearSSSP.Decremental.AdapterState i}
  {xs : List.{0} (Fin i.n)} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
    @LE.le.{0} Nat instLENat i.n B →
      (∀ (address : Nat),
          @LT.lt.{0} Nat instLTNat address
              (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                  reserve N).utility →
            And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
              (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
        @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182)))) →
          @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180)))) →
            DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs t) ∧ (DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.ReportDecode.code)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve N : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (a : DecrAlmostLinearSSSP.Decremental.AdapterState i) (xs : List.{0} (Fin i.n))
          (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
            DecrAlmostLinearSSSP.Decremental.Native.Globals i B
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).utility
                s →
              (∀ (z : Fin i.n),
                  DecrAlmostLinearSSSP.Decremental.PointerValid i
                    (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a) z
                    (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a z)) →
                ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n)
                  (g : DecrAlmostLinearSSSP.Decremental.Machine),
                  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B
                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s g.natMem g.realMem →
                    (∀ (z : Fin i.n),
                        And
                          (@LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n z))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@Eq.{1} Nat (g.natMem (@Fin.val i.n z))
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                            @LE.le.{0} Real Real.instLE
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                              (g.realMem (@Fin.val i.n z)))) →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 198) (instOfNatNat (nat_lit 198))))
                          (DecrAlmostLinearSSSP.Decremental.bankAddress B
                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) (@Fin.val i.n v)) →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                            (DecrAlmostLinearSSSP.Decremental.bankFactor
                              (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)) →
                          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108))))
                              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                                (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).cache
                                i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)) →
                            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))))
                                (DecrAlmostLinearSSSP.Decremental.delta i
                                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)) →
                              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
                                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).pointer →
                                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
                                    (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                        (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).flags →
                                  ∃ cost t ys,
                                    And
                                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                        DecrAlmostLinearSSSP.Decremental.Native.decodedReportEvent s cost t)
                                      (And
                                        (@LE.le.{0} Nat instLENat cost
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
                                                (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                                  (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i
                                                    (DecrAlmostLinearSSSP.Decremental.adapterWrite i a j v
                                                      (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val i.n v)))
                                                    v)
                                                  (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a v))))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 55) (instOfNatNat (nat_lit 55)))))
                                        (And
                                          (DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N
                                            (DecrAlmostLinearSSSP.Decremental.adapterWrite i a j v
                                              (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val i.n v)))
                                            ys t)
                                          (And
                                            (@Eq.{1} (List.{0} (Fin i.n)) ys
                                              (@ite.{1} (List.{0} (Fin i.n))
                                                (@Membership.mem.{0, 0} (Fin i.n) (List.{0} (Fin i.n))
                                                  (@List.instMembership.{0} (Fin i.n)) xs v)
                                                (@List.instDecidableMemOfLawfulBEq.{0} (Fin i.n)
                                                  (@instBEqOfDecidableEq.{0} (Fin i.n) (instDecidableEqFin i.n))
                                                  (@Std.LawfulBEqOrd.lawfulBEq.{0} (Fin i.n)
                                                    (@instBEqOfDecidableEq.{0} (Fin i.n) (instDecidableEqFin i.n))
                                                    (instOrdFin i.n)
                                                    (@Std.LawfulBCmp.toLawfulBEqCmp.{0} (Fin i.n)
                                                      (@Preorder.toLE.{0} (Fin i.n)
                                                        (@PartialOrder.toPreorder.{0} (Fin i.n)
                                                          (@LinearOrder.toPartialOrder.{0} (Fin i.n)
                                                            (@Fin.instLinearOrder i.n))))
                                                      (@Preorder.toLT.{0} (Fin i.n)
                                                        (@PartialOrder.toPreorder.{0} (Fin i.n)
                                                          (@LinearOrder.toPartialOrder.{0} (Fin i.n)
                                                            (@Fin.instLinearOrder i.n))))
                                                      (@instBEqOfDecidableEq.{0} (Fin i.n) (instDecidableEqFin i.n))
                                                      (@Ord.compare.{0} (Fin i.n) (instOrdFin i.n))
                                                      (@instLawfulBCmpCompare_mathlib.{0} (Fin i.n)
                                                        (@Fin.instLinearOrder i.n)))
                                                    (Fin.instLawfulEqOrd i.n))
                                                  v xs)
                                                xs
                                                (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin i.n)) (List.{0} (Fin i.n))
                                                  (List.{0} (Fin i.n))
                                                  (@instHAppendOfAppend.{0} (List.{0} (Fin i.n))
                                                    (@List.instAppend.{0} (Fin i.n)))
                                                  xs (@List.cons.{0} (Fin i.n) v (@List.nil.{0} (Fin i.n))))))
                                            (∀ (address : Nat),
                                              @Ne.{1} Nat address
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                                                      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                                          (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                                          N).cache
                                                      i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      (@Fin.val i.n v))) →
                                                Not
                                                    (DecrAlmostLinearSSSP.Decremental.Native.PointerArrayCell
                                                      (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                                        (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N)
                                                      i.n address) →
                                                  (∀ (r : Nat),
                                                      @Ne.{1} Nat address
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                                                                (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve
                                                                N).utility
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              r))
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1))))) →
                                                    And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                      (@Eq.{1} Real (t.realMem address) (s.realMem address))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.fields s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.fieldData s)))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.fieldData s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 212) (instOfNatNat (nat_lit 212))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.fieldData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 210) (instOfNatNat (nat_lit 210))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92)))))
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.fieldData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 214) (instOfNatNat (nat_lit 214))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (B j start count : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
            (DecrAlmostLinearSSSP.Decremental.bankFactor j) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) i.n →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92)))) start →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))) count →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                    ∃ cost t,
                      And
                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                          DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.setup s cost t)
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
                              (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))))
                          (And
                            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 212) (instOfNatNat (nat_lit 212))))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (DecrAlmostLinearSSSP.Decremental.bankFactor j)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                            (And
                              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 210) (instOfNatNat (nat_lit 210))))
                                start)
                              (And
                                (@Eq.{1} Nat
                                  (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 214) (instOfNatNat (nat_lit 214)))) count)
                                (∀ (address : Nat),
                                  (∀ (a : Nat),
                                      @Ne.{1} Nat address
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                    And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                      (@Eq.{1} Real (t.realMem address) (s.realMem address))))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.finish s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.finished s)) ∧ ((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 94) (instOfNatNat (nat_lit 94))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 128) (instOfNatNat (nat_lit 128))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 132) (instOfNatNat (nat_lit 132))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 38) (instOfNatNat (nat_lit 38))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
                  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 130) (instOfNatNat (nat_lit 130))) →
                    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
                      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24))) →
                        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 196) (instOfNatNat (nat_lit 196))) →
                          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
                            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))) →
                              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) →
                                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 42) (instOfNatNat (nat_lit 42))) →
                                  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 44) (instOfNatNat (nat_lit 44))) →
                                    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 46) (instOfNatNat (nat_lit 46))) →
                                      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 186) (instOfNatNat (nat_lit 186))) →
                                        @Ne.{1} Nat k
                                            (@OfNat.ofNat.{0} Nat (nat_lit 184) (instOfNatNat (nat_lit 184))) →
                                          @Ne.{1} Nat k
                                              (@OfNat.ofNat.{0} Nat (nat_lit 188) (instOfNatNat (nat_lit 188))) →
                                            @Ne.{1} Nat k
                                                (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))) →
                                              @Ne.{1} Nat k
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 182) (instOfNatNat (nat_lit 182))) →
                                                DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                                                  DecrAlmostLinearSSSP.Decremental.Native.decodedReportEvent k) ∧ (And
  (DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Native.decodedReportEvent
    (@OfNat.ofNat.{0} Nat (nat_lit 210) (instOfNatNat (nat_lit 210))))
  (And
    (DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Native.decodedReportEvent
      (@OfNat.ofNat.{0} Nat (nat_lit 212) (instOfNatNat (nat_lit 212))))
    (DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Native.decodedReportEvent
      (@OfNat.ofNat.{0} Nat (nat_lit 214) (instOfNatNat (nat_lit 214)))))))))) ∧ ((((DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.Native.decodedReportEvent) ∧ (DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.finish)) ∧ ((DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.body) ∧ (∀ (B bank : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (address : Nat),
  @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
      (DecrAlmostLinearSSSP.Decremental.physicalWrites B bank ins g) address →
    ∃ a, @Eq.{1} Nat address (DecrAlmostLinearSSSP.Decremental.bankAddress B bank a)))) ∧ (((∀ (B bank : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (steps address : Nat),
  @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
      (DecrAlmostLinearSSSP.Decremental.physicalTraceWrites B bank p g steps) address →
    ∃ a, @Eq.{1} Nat address (DecrAlmostLinearSSSP.Decremental.bankAddress B bank a)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B bank a : Nat),
  @Eq.{1} (Option.{0} (Fin i.n))
    (DecrAlmostLinearSSSP.Decremental.publicReport i B bank (DecrAlmostLinearSSSP.Decremental.bankAddress B bank a))
    (@dite.{1} (Option.{0} (Fin i.n)) (@LT.lt.{0} Nat instLTNat a i.n) (a.decLt i.n)
      (fun h => @Option.some.{0} (Fin i.n) (@Fin.mk i.n a h)) fun h => @Option.none.{0} (Fin i.n)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B reserve N j : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j s s) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j : Nat}
  {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j s t →
    DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j t u →
      DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j s u) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j s t →
    ∀ (address : Nat),
      @LE.le.{0} Nat instLENat address B →
        And (@Eq.{1} Nat (t.natMem address) (s.natMem address)) (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))) ∧ (((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j s t →
    ∀ (q v : Nat),
      And
        (@Eq.{1} Nat (t.natMem (DecrAlmostLinearSSSP.Decremental.bankAddress B q v))
          (s.natMem (DecrAlmostLinearSSSP.Decremental.bankAddress B q v)))
        (@Eq.{1} Real (t.realMem (DecrAlmostLinearSSSP.Decremental.bankAddress B q v))
          (s.realMem (DecrAlmostLinearSSSP.Decremental.bankAddress B q v)))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N j q : Nat}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N j s t →
    DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B q s g.natMem g.realMem →
      DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B q t g.natMem g.realMem)) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N : Nat}
  {j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N
      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t →
    ∀ (r : Nat),
      @LE.le.{0} Nat instLENat r reserve →
        @Eq.{1} Nat
          (t.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                  reserve N).reports
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)))
          (s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n (DecrAlmostLinearSSSP.Decremental.scaleCount i)
                  reserve N).reports
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r)))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i),
  (∀ (v : Fin i.n),
      DecrAlmostLinearSSSP.Decremental.PointerValid i (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i s) v
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s v)) →
    @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.pointerEnergy i s)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n
        (DecrAlmostLinearSSSP.Decremental.scaleCount i))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (value : ENNReal),
  @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.pointerEnergy i s)
    (DecrAlmostLinearSSSP.Decremental.pointerEnergy i (DecrAlmostLinearSSSP.Decremental.adapterWrite i s j v value))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (value : ENNReal),
  @LE.le.{0} Nat instLENat
    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
      (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i
        (DecrAlmostLinearSSSP.Decremental.adapterWrite i s j v value) v)
      (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s v))
    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
      (DecrAlmostLinearSSSP.Decremental.pointerEnergy i (DecrAlmostLinearSSSP.Decremental.adapterWrite i s j v value))
      (DecrAlmostLinearSSSP.Decremental.pointerEnergy i s)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (events : List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i)),
  (∀ (v : Fin i.n),
      DecrAlmostLinearSSSP.Decremental.PointerValid i (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i s) v
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s v)) →
    ∀ (v : Fin i.n),
      DecrAlmostLinearSSSP.Decremental.PointerValid i
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
          (DecrAlmostLinearSSSP.Decremental.adapterTrace i s events))
        v
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i
          (DecrAlmostLinearSSSP.Decremental.adapterTrace i s events) v)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (events : List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i)),
  @LE.le.{0} Nat instLENat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (DecrAlmostLinearSSSP.Decremental.pointerTravel i s events) (DecrAlmostLinearSSSP.Decremental.pointerEnergy i s))
    (DecrAlmostLinearSSSP.Decremental.pointerEnergy i (DecrAlmostLinearSSSP.Decremental.adapterTrace i s events))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (events : List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i)),
  (∀ (v : Fin i.n),
      DecrAlmostLinearSSSP.Decremental.PointerValid i (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i s) v
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i s v)) →
    @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.pointerTravel i s events)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n
        (DecrAlmostLinearSSSP.Decremental.scaleCount i))))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (events : List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
  (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
  @LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i s j v)
    (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i (DecrAlmostLinearSSSP.Decremental.adapterTrace i s events)
      j v)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (value : ENNReal),
  @LE.le.{0} ENNReal ENNReal.instLE value
    (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
      (DecrAlmostLinearSSSP.Decremental.adapterWrite i s j v value) j v))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (events : List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
  (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (value : ENNReal),
  @Membership.mem.{0, 0}
      (Prod.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal))
      (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
      (@List.instMembership.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i)) events
      (@Prod.mk.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal) j
        (@Prod.mk.{0, 0} (Fin i.n) ENNReal v value)) →
    @LE.le.{0} ENNReal ENNReal.instLE value
      (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
        (DecrAlmostLinearSSSP.Decremental.adapterTrace i s events) j v)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  (∀ (v : Fin i.n),
      @LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val i.n v))
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i s j v)) →
    ∀ (v : Fin i.n),
      @LE.le.{0} ENNReal ENNReal.instLE
        (DecrAlmostLinearSSSP.Decremental.stored (DecrAlmostLinearSSSP.Decremental.execute p c t) (@Fin.val i.n v))
        (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
          (DecrAlmostLinearSSSP.Decremental.adapterTrace i s
            (DecrAlmostLinearSSSP.Decremental.observedAdapterEvents i j p c t))
          j v)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (xs ys : List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i)),
  @Eq.{1} (DecrAlmostLinearSSSP.Decremental.AdapterState i)
    (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
      (@HAppend.hAppend.{0, 0, 0} (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
        (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
        (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
        (@instHAppendOfAppend.{0} (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
          (@List.instAppend.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i)))
        xs ys))
    (DecrAlmostLinearSSSP.Decremental.adapterTrace i (DecrAlmostLinearSSSP.Decremental.adapterTrace i a xs) ys))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (xs ys : List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i)),
  @Eq.{1} Nat
    (DecrAlmostLinearSSSP.Decremental.pointerTravel i a
      (@HAppend.hAppend.{0, 0, 0} (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
        (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
        (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
        (@instHAppendOfAppend.{0} (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
          (@List.instAppend.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i)))
        xs ys))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (DecrAlmostLinearSSSP.Decremental.pointerTravel i a xs)
      (DecrAlmostLinearSSSP.Decremental.pointerTravel i (DecrAlmostLinearSSSP.Decremental.adapterTrace i a xs) ys))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (xs : List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i)),
  DecrAlmostLinearSSSP.Decremental.OutputConsistent i a →
    DecrAlmostLinearSSSP.Decremental.OutputConsistent i (DecrAlmostLinearSSSP.Decremental.adapterTrace i a xs))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve N : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (a : DecrAlmostLinearSSSP.Decremental.AdapterState i) (xs : List.{0} (Fin i.n))
          (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
            DecrAlmostLinearSSSP.Decremental.Native.Globals i B
                (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).utility
                s →
              (∀ (z : Fin i.n),
                  DecrAlmostLinearSSSP.Decremental.PointerValid i
                    (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a) z
                    (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a z)) →
                ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (logical : Nat)
                  (g : DecrAlmostLinearSSSP.Decremental.Machine),
                  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B
                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s g.natMem g.realMem →
                    (∀ (z : Fin i.n),
                        And
                          (@LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n z))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@Eq.{1} Nat (g.natMem (@Fin.val i.n z))
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                            @LE.le.{0} Real Real.instLE
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                              (g.realMem (@Fin.val i.n z)))) →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 198) (instOfNatNat (nat_lit 198))))
                          (DecrAlmostLinearSSSP.Decremental.bankAddress B
                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) logical) →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                            (DecrAlmostLinearSSSP.Decremental.bankFactor
                              (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)) →
                          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108))))
                              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                                (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).cache
                                i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)) →
                            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))))
                                (DecrAlmostLinearSSSP.Decremental.delta i
                                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)) →
                              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
                                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).pointer →
                                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
                                    (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                        (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).flags →
                                  @Eq.{1} Nat
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 212) (instOfNatNat (nat_lit 212))))
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (DecrAlmostLinearSSSP.Decremental.bankFactor
                                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                                    ∃ cost t ys,
                                      And
                                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                          DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.action s cost t)
                                        (And
                                          (@LE.le.{0} Nat instLENat cost
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
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                                  (DecrAlmostLinearSSSP.Decremental.pointerTravel i a
                                                    (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.events i B j
                                                      g
                                                      (DecrAlmostLinearSSSP.Decremental.bankAddress B
                                                        (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)
                                                        logical)))))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))))
                                          (And
                                            (DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N
                                              (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
                                                (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.events i B j g
                                                  (DecrAlmostLinearSSSP.Decremental.bankAddress B
                                                    (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)
                                                    logical)))
                                              ys t)
                                            (And
                                              (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin i.n) ys)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@List.length.{0} (Fin i.n) xs)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N
                                                (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t))))) ∧ ((∀ (k : Nat),
  @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
      DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.fixedNat k →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.body k) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.action
  (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))))))))) ∧ ((((((DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.body
  (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N cost : Nat}
  {j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)} {g : DecrAlmostLinearSSSP.Decremental.Machine}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment i B reserve N j g s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.body s cost
        t →
      DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N
          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t →
        DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment i B reserve N j g t)) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B reserve N offset address : Nat} {rest : List.{0} Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue i B reserve N offset (@List.cons.{0} Nat address rest) s →
    @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 210) (instOfNatNat (nat_lit 210))))) address) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve N offset : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (a : DecrAlmostLinearSSSP.Decremental.AdapterState i) (xs : List.{0} (Fin i.n))
          (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
            ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (g : DecrAlmostLinearSSSP.Decremental.Machine),
              DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment i B reserve N j g s →
                (∀ (z : Fin i.n),
                    DecrAlmostLinearSSSP.Decremental.PointerValid i
                      (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a) z
                      (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a z)) →
                  (∀ (z : Fin i.n),
                      And
                        (@LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n z))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@Eq.{1} Nat (g.natMem (@Fin.val i.n z))
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                          @LE.le.{0} Real Real.instLE
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                            (g.realMem (@Fin.val i.n z)))) →
                    ∀ (logical : Nat) (rest : List.{0} Nat),
                      DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue i B reserve N offset
                          (@List.cons.{0} Nat
                            (DecrAlmostLinearSSSP.Decremental.bankAddress B
                              (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) logical)
                            rest)
                          s →
                        ∃ cost t ys,
                          And
                            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                              DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.body s cost t)
                            (And
                              (@LE.le.{0} Nat instLENat cost
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
                                      (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                      (DecrAlmostLinearSSSP.Decremental.pointerTravel i a
                                        (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.events i B j g
                                          (DecrAlmostLinearSSSP.Decremental.bankAddress B
                                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) logical)))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 59) (instOfNatNat (nat_lit 59)))))
                              (And
                                (DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N
                                  (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
                                    (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.events i B j g
                                      (DecrAlmostLinearSSSP.Decremental.bankAddress B
                                        (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) logical)))
                                  ys t)
                                (And
                                  (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin i.n) ys)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@List.length.{0} (Fin i.n) xs)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (And
                                    (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment i B reserve N j g
                                      t)
                                    (And
                                      (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue i B reserve N
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                        rest t)
                                      (DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N
                                        (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t))))))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B : Nat) (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i))
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (address : Nat) (rest : List.{0} Nat),
  @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
    (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.allEvents i B j g (@List.cons.{0} Nat address rest))
    (@HAppend.hAppend.{0, 0, 0} (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
      (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
      (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
      (@instHAppendOfAppend.{0} (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
        (@List.instAppend.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i)))
      (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.events i B j g address)
      (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.allEvents i B j g rest))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B : Nat) (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i))
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (reports : List.{0} Nat),
  @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
    (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.allEvents i B j g reports)
    (@List.map.{0, 0} (Fin i.n)
      (Prod.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal))
      (fun v =>
        @Prod.mk.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal) j
          (@Prod.mk.{0, 0} (Fin i.n) ENNReal v (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val i.n v))))
      (DecrAlmostLinearSSSP.Decremental.publicReports i B (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)
        reports)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve N : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (g : DecrAlmostLinearSSSP.Decremental.Machine),
          (∀ (z : Fin i.n),
              And
                (@LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n z))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Eq.{1} Nat (g.natMem (@Fin.val i.n z)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                  @LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (g.realMem (@Fin.val i.n z)))) →
            ∀ (reports : List.{0} Nat),
              (∀ (address : Nat),
                  @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) reports address →
                    ∃ logical,
                      @Eq.{1} Nat address
                        (DecrAlmostLinearSSSP.Decremental.bankAddress B
                          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) logical)) →
                ∀ (a : DecrAlmostLinearSSSP.Decremental.AdapterState i) (xs : List.{0} (Fin i.n))
                  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (offset : Nat),
                  DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
                    DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment i B reserve N j g s →
                      (∀ (z : Fin i.n),
                          DecrAlmostLinearSSSP.Decremental.PointerValid i
                            (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a) z
                            (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a z)) →
                        DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue i B reserve N offset reports s →
                          ∃ cost t ys,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.loop s cost t)
                              (And
                                (@LE.le.{0} Nat instLENat cost
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
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
                                          (@OfNat.ofNat.{0} Nat (nat_lit 61) (instOfNatNat (nat_lit 61))))
                                        (@List.length.{0} Nat reports))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                        (DecrAlmostLinearSSSP.Decremental.pointerTravel i a
                                          (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.allEvents i B j g
                                            reports))))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                (And
                                  (DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N
                                    (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
                                      (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.allEvents i B j g reports))
                                    ys t)
                                  (And
                                    (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin i.n) ys)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@List.length.{0} (Fin i.n) xs) (@List.length.{0} Nat reports)))
                                    (And
                                      (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment i B reserve N j
                                        g t)
                                      (And
                                        (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Queue i B reserve N
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                            (@List.length.{0} Nat reports))
                                          (@List.nil.{0} Nat) t)
                                        (DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N
                                          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s t))))))) ∧ ((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 210) (instOfNatNat (nat_lit 210))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 212) (instOfNatNat (nat_lit 212))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 214) (instOfNatNat (nat_lit 214))) →
                DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                  DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.setup k) ∧ (∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
            DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.setup k))))) ∧ ((((DecrAlmostLinearSSSP.Decremental.Native.GlobalFrame DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.setup) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B reserve N : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (g : DecrAlmostLinearSSSP.Decremental.Machine)
          (reports : List.{0} Nat),
          (∀ (address : Nat),
              @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) reports address →
                ∃ logical,
                  @Eq.{1} Nat address
                    (DecrAlmostLinearSSSP.Decremental.bankAddress B
                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) logical)) →
            (∀ (z : Fin i.n),
                And
                  (@LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n z))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Eq.{1} Nat (g.natMem (@Fin.val i.n z))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                    @LE.le.{0} Real Real.instLE
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                      (g.realMem (@Fin.val i.n z)))) →
              ∀ (a : DecrAlmostLinearSSSP.Decremental.AdapterState i) (xs : List.{0} (Fin i.n))
                (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
                DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N a xs s →
                  DecrAlmostLinearSSSP.Decremental.Native.Globals i B
                      (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                          (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).utility
                      s →
                    (∀ (z : Fin i.n),
                        DecrAlmostLinearSSSP.Decremental.PointerValid i
                          (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a) z
                          (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i a z)) →
                      DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B
                          (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s g.natMem g.realMem →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                            (DecrAlmostLinearSSSP.Decremental.bankFactor
                              (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)) →
                          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108))))
                              (DecrAlmostLinearSSSP.Decremental.Native.cacheAt
                                (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                    (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).cache
                                i.n (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)) →
                            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))))
                                (DecrAlmostLinearSSSP.Decremental.delta i
                                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j)) →
                              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 96) (instOfNatNat (nat_lit 96))))
                                  (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                      (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).pointer →
                                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98))))
                                    (DecrAlmostLinearSSSP.Decremental.Native.pointerLayout B i.n
                                        (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).flags →
                                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92))))
                                      (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                                          (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).reports →
                                    DecrAlmostLinearSSSP.Decremental.ReportLog
                                        (DecrAlmostLinearSSSP.Decremental.Native.scaleLayout B i.n
                                            (DecrAlmostLinearSSSP.Decremental.scaleCount i) reserve N).reports
                                        reports s →
                                      @LE.le.{0} Nat instLENat (@List.length.{0} Nat reports) reserve →
                                        ∃ cost t ys,
                                          And
                                            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                              DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.code s cost t)
                                            (And
                                              (@LE.le.{0} Nat instLENat cost
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
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
                                                              (instOfNatNat (nat_lit 32)))))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 61) (instOfNatNat (nat_lit 61))))
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@List.length.{0} Nat reports)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                                      (DecrAlmostLinearSSSP.Decremental.pointerTravel i a
                                                        (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.allEvents
                                                          i B j g reports))))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                              (And
                                                (DecrAlmostLinearSSSP.Decremental.Native.AdapterMemory i B reserve N
                                                  (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
                                                    (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.allEvents i B
                                                      j g reports))
                                                  ys t)
                                                (And
                                                  (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin i.n) ys)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@List.length.{0} (Fin i.n) xs) (@List.length.{0} Nat reports)))
                                                  (And
                                                    (DecrAlmostLinearSSSP.Decremental.Native.ReportConsume.Environment i
                                                      B reserve N j g t)
                                                    (And
                                                      (@Eq.{1} Nat
                                                        (t.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 214)
                                                            (instOfNatNat (nat_lit 214))))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                                      (DecrAlmostLinearSSSP.Decremental.Native.ReportFrame i B reserve N
                                                        (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) j) s
                                                        t)))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
    (DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.result s)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (j record cache next : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106)))) record →
    DecrAlmostLinearSSSP.Decremental.Native.RecordImage i j record cache next s →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.result s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
            (DecrAlmostLinearSSSP.Decremental.bankFactor j))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.result s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108))))
              cache)
            (And
              (@Eq.{1} Real
                ((DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.result s).realReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))))
                (DecrAlmostLinearSSSP.Decremental.delta i j))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.result s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) record
                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
                (And
                  (DecrAlmostLinearSSSP.Decremental.ReportLog
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92)))) (@List.nil.{0} Nat)
                    (DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.result s))
                  (@Eq.{1} Nat
                    ((DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.result s).natReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.code)))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 108) (instOfNatNat (nat_lit 108))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) →
                  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                    DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.code k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Native.UpdateHeader.code k)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Native.SavedDeletion.suffix s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Native.SavedDeletion.patched s)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (F e N : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))) F →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78)))) e →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast e)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                N) →
            (∀ (j : Nat),
                @LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.registerBound p.code) →
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
                  @LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.registerBound p.code) →
                    @LT.lt.{0} Nat instLTNat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))) →
                ∃ cost t,
                  And
                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                      DecrAlmostLinearSSSP.Decremental.Native.SavedDeletion.code s cost t)
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
                          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                      (And
                        (∀ (j : Nat),
                          @LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.registerBound p.code) →
                            And
                              (@Eq.{1} Nat
                                (t.natMem
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                                  ((DecrAlmostLinearSSSP.Decremental.deletionMachine p g e).natReg j)))
                              (@Eq.{1} Real
                                (t.realMem
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                                ((DecrAlmostLinearSSSP.Decremental.deletionMachine p g e).realReg j)))
                        (∀ (address : Nat),
                          @Ne.{1} Nat address
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))) →
                            (∀ (a : Nat),
                                @Ne.{1} Nat address
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                              And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                (@Eq.{1} Real (t.realMem address) (s.realMem address)))))) ∧ (∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 208) (instOfNatNat (nat_lit 208))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                DecrAlmostLinearSSSP.Decremental.Native.SavedDeletion.code k)))))) ∧ (((((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
            DecrAlmostLinearSSSP.Decremental.Native.SavedDeletion.code k) ∧ (∀ {B F : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (cost : Nat),
              DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  ((DecrAlmostLinearSSSP.Decremental.shadowAction ins).seq
                    DecrAlmostLinearSSSP.Decremental.appendStoreReport)
                  s cost t →
                ∀ (address : Nat),
                  (∀ (a : Nat),
                      @Ne.{1} Nat address
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
                    @Ne.{1} Nat address (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))) →
                      And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                        (@Eq.{1} Nat (t.natMem address) (s.natMem address)))) ∧ ((∀ {B F : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (cost : Nat),
              DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.observedAction ins) s
                  cost t →
                ∀ (address : Nat),
                  (∀ (a : Nat),
                      @Ne.{1} Nat address
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
                    @Ne.{1} Nat address (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))) →
                      And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                        (@Eq.{1} Nat (t.natMem address) (s.natMem address))) ∧ (∀ {B F : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (cost : Nat),
              DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  (DecrAlmostLinearSSSP.Decremental.observedInstruction g.pc ins) s cost t →
                ∀ (address : Nat),
                  (∀ (a : Nat),
                      @Ne.{1} Nat address
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
                    @Ne.{1} Nat address (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))) →
                      And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                        (@Eq.{1} Nat (t.natMem address) (s.natMem address))))) ∧ (((∀ {B F : Nat} (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc : Nat)
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (g : DecrAlmostLinearSSSP.Decremental.Machine),
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            @LE.le.{0} Nat instLENat pc g.pc →
              ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code
                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) g.pc pc))
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
                  ∀ (cost : Nat),
                    DecrAlmostLinearSSSP.Decremental.Structured.Eval
                        (DecrAlmostLinearSSSP.Decremental.observedDispatchAux pc code) s cost t →
                      ∀ (address : Nat),
                        (∀ (a : Nat),
                            @Ne.{1} Nat address
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
                          @Ne.{1} Nat address
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))) →
                            And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                              (@Eq.{1} Nat (t.natMem address) (s.natMem address))) ∧ (∀ (guest : DecrAlmostLinearSSSP.Decremental.Program) (steps B bank start : Nat)
  (s u : DecrAlmostLinearSSSP.Decremental.Structured.Data) (g : DecrAlmostLinearSSSP.Decremental.Machine),
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
                    @LE.le.{0} Nat instLENat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                      (∀ (j : Nat),
                          @LT.lt.{0} Nat instLTNat j steps →
                            @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute guest g j).halted Bool.false →
                              ∃ ins,
                                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                    Nat DecrAlmostLinearSSSP.Decremental.Instruction
                                    (fun as i =>
                                      @LT.lt.{0} Nat instLTNat i
                                        (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                                    guest.code (DecrAlmostLinearSSSP.Decremental.execute guest g j).pc)
                                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins)) →
                        @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute guest g steps).halted Bool.true →
                          ∀ (cost : Nat),
                            DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                (DecrAlmostLinearSSSP.Decremental.observedInterpreter guest.code) s cost u →
                              ∀ (address : Nat),
                                (∀ (a : Nat),
                                    @Ne.{1} Nat address
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
                                  (∀ (j : Nat),
                                      @LE.le.{0} Nat instLENat j
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@List.length.{0} Nat reports)
                                            (@List.length.{0} Nat
                                              (DecrAlmostLinearSSSP.Decremental.physicalTraceWrites B bank guest g
                                                steps))) →
                                        @Ne.{1} Nat address
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))) →
                                    And (@Eq.{1} Real (u.realMem address) (s.realMem address))
                                      (@Eq.{1} Nat (u.natMem address) (s.natMem address)))) ∧ ((∀ (guest : DecrAlmostLinearSSSP.Decremental.Program) (B bank start : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (g final : DecrAlmostLinearSSSP.Decremental.Machine),
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
                    @LE.le.{0} Nat instLENat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                      DecrAlmostLinearSSSP.Decremental.Ends guest g final →
                        ∃ cost u t,
                          And
                            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                              (DecrAlmostLinearSSSP.Decremental.observedInterpreter guest.code) s cost u)
                            (And
                              (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                (DecrAlmostLinearSSSP.Decremental.execute guest g t) final)
                              (And
                                (@Eq.{1} Nat t
                                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) final.work g.work))
                                (And
                                  (@LE.le.{0} Nat instLENat cost
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (DecrAlmostLinearSSSP.Decremental.observedDispatchCharge guest.code)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) final.work
                                          g.work))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                  (And
                                    (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                                      (DecrAlmostLinearSSSP.Decremental.bankFactor bank) u final)
                                    (And
                                      (DecrAlmostLinearSSSP.Decremental.ReportLog start
                                        (@HAppend.hAppend.{0, 0, 0} (List.{0} Nat) (List.{0} Nat) (List.{0} Nat)
                                          (@instHAppendOfAppend.{0} (List.{0} Nat) (@List.instAppend.{0} Nat)) reports
                                          (DecrAlmostLinearSSSP.Decremental.physicalTraceWrites B bank guest g t))
                                        u)
                                      (∀ (address : Nat),
                                        (∀ (a : Nat),
                                            @Ne.{1} Nat address
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
                                          (∀ (j : Nat),
                                              @LE.le.{0} Nat instLENat j
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@List.length.{0} Nat reports)
                                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                                      final.work g.work)) →
                                                @Ne.{1} Nat address
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      j))) →
                                            And (@Eq.{1} Real (u.realMem address) (s.realMem address))
                                              (@Eq.{1} Nat (u.natMem address) (s.natMem address))))))))) ∧ ((∀ (B bank other a : Nat),
  @Ne.{1} Nat other bank →
    ∀ (b : Nat),
      @Ne.{1} Nat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (DecrAlmostLinearSSSP.Decremental.bankFactor other)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ (∀ (B other a start : Nat),
  (∃ r,
      @Eq.{1} Nat start
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    ∀ (j : Nat),
      @Ne.{1} Nat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (DecrAlmostLinearSSSP.Decremental.bankFactor other)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))))))) ∧ ((((∀ (B bank start address : Nat),
  @LE.le.{0} Nat instLENat address B →
    (∃ r,
        @Eq.{1} Nat start
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      And
        (∀ (a : Nat),
          @Ne.{1} Nat address
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        (∀ (j : Nat),
          @Ne.{1} Nat address
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))) ∧ (∀ (B bank start address : Nat),
  (∃ a,
      @Eq.{1} Nat address
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    @LT.lt.{0} Nat instLTNat address start →
      And
        (∀ (a : Nat),
          @Ne.{1} Nat address
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (DecrAlmostLinearSSSP.Decremental.bankFactor bank)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        (∀ (j : Nat),
          @Ne.{1} Nat address
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))))) ∧ ((∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.observedAction ins) k) ∧ ((∀ (pc : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.observedInstruction pc ins)
        k) ∧ (∀ (xs : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc k : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.observedDispatchAux pc xs)
        k)))) ∧ (((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.observedInterpreter p.code)
        k) ∧ (∀ (N entry B bank start : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
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
                                  ∃ cost steps t,
                                    And
                                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                        (DecrAlmostLinearSSSP.Decremental.ObservedSourceCall.code N entry p) s cost t)
                                      (And
                                        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                          (DecrAlmostLinearSSSP.Decremental.execute p g steps) final)
                                        (And
                                          (@Eq.{1} Nat steps
                                            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) final.work
                                              g.work))
                                          (And
                                            (@LE.le.{0} Nat instLENat cost
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (DecrAlmostLinearSSSP.Decremental.observedDispatchCharge p.code)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                                      final.work g.work))
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) N))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))
                                            (And
                                              (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                                                (DecrAlmostLinearSSSP.Decremental.bankFactor bank) t final)
                                              (And
                                                (DecrAlmostLinearSSSP.Decremental.ReportLog start
                                                  (DecrAlmostLinearSSSP.Decremental.physicalTraceWrites B bank p g
                                                    steps)
                                                  t)
                                                (∀ (address : Nat),
                                                  (∀ (a : Nat),
                                                      @Ne.{1} Nat address
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          B
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
                                                              (@instHSub.{0} Nat instSubNat) final.work g.work) →
                                                          @Ne.{1} Nat address
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) start
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                j))) →
                                                      And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                                                        (@Eq.{1} Nat (t.natMem address) (s.natMem address)))))))))) ∧ ((∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @Even.{0} Nat instAddNat k →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.observedAction ins) k) ∧ ((∀ (xs : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc k : Nat),
  @Even.{0} Nat instAddNat k →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.observedDispatchAux pc xs) k) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @Even.{0} Nat instAddNat k →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.observedInterpreter p.code)
      k)))))))) := by sorry
