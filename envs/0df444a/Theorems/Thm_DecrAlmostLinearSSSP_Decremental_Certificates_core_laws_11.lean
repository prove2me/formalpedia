-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_11
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T17:33:24.129965+00:00
-- url     : https://prove2.me/theorems/1b287abd-a072-485e-b53d-cc40417d41cb
-- title:
--   Terminating native repair and computable cut quality
-- statement:
--   Let the graph, labels, caches, cut states and scalar RAM machines be the objects of the normalized decremental SSSP implementation interface. Each component below is universally quantified over its own parameters and representation hypotheses.
--
--   Each native repair-body execution follows an actual refresh, toggle or stop transition and decreases the well-founded repair rank. The resulting finite loop terminates in a certified stopping state. Credit and operation-debt inequalities account for calls, reports and toggles, while finite native routines compute the cut-quality envelope and preserve the protected machine state.
--
--   All component assertions in this collection hold simultaneously:
--
--   $$
--   \bigwedge_{j\in J} L_j.
--   $$
--
--   The assertions $L_j$ are the exact execution, mathematical comparison, memory-image, preservation and charged-work contracts described above. A supplied source-execution or cut-implementation hypothesis is retained wherever it is used; correctness, termination and work of the host operations are conclusions of the corresponding contracts.
--
--   **Formalization Note** A balanced conjunction makes the individually quantified component laws available by short projections. These are implementation contracts for the cited proof and reductions, rather than separate numbered claims attributed to the source.
-- source:
--   Cui, Li, Miao and Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, October 2026 submission #912, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf, p.4 unnumbered normalization reductions; Theorem 3.1 p.6; Sections 3.1-3.5 pp.7-17, including Lemmas 3.2-3.8; Lemma 4.1 p.18 scalar unit-cost RAM model. Component laws verify the explicit finite programs and memory representations in DecrAlmostLinearSSSP_CoreRAMFoundation.

import Definitions.Def_DecrAlmostLinearSSSP_CoreRAMFoundation
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable

theorem DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_11 : (((((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
    DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K
      (@DecrAlmostLinearSSSP.Decremental.State.mk b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
        (@DecrAlmostLinearSSSP.Decremental.State.y b s) (@DecrAlmostLinearSSSP.Decremental.State.cache b s)
        (@DecrAlmostLinearSSSP.Decremental.State.baseline b s)
        (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
        (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b s)
        (@DecrAlmostLinearSSSP.Decremental.State.sample b s) (@DecrAlmostLinearSSSP.Decremental.State.output b s)
        (@DecrAlmostLinearSSSP.Decremental.State.pending b s) Bool.true
        (@DecrAlmostLinearSSSP.Decremental.State.toggles b s) (@DecrAlmostLinearSSSP.Decremental.State.history b s))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreNativeCut.stopCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.stoppedData s))) ∧ ((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N m exponent : Nat} {K K0 ξ h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (ctx : DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context b B N m exponent impl K0 ξ h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K state →
        @DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
            (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) state
            (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent impl K0 ξ h Γ init s
                ctx)) →
          @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b state) Bool.false →
            @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
                (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
              Or
                  (@Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (∃ r,
                    And
                      (@DecrAlmostLinearSSSP.Decremental.RatioGuarantee b.input.n
                        (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                          (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                            (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
                        (DecrAlmostLinearSSSP.Decremental.cachedPhysical b state) K
                        (@DecrAlmostLinearSSSP.Decremental.CutReply.G b r)
                        (@DecrAlmostLinearSSSP.Decremental.CutReply.U b r)
                        (@DecrAlmostLinearSSSP.Decremental.CutReply.cut b r))
                      (@LE.le.{0} Real Real.instLE
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@Neg.neg.{0} Real Real.instNeg
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 4)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                            K))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@DecrAlmostLinearSSSP.Decremental.CutReply.G b r)
                          (@DecrAlmostLinearSSSP.Decremental.CutReply.U b r)))) →
                ∃ next,
                  And
                    (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                      (@DecrAlmostLinearSSSP.Decremental.State.mk b
                        (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.y b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.cache b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.output b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.pending b state) Bool.true
                        (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.history b state))
                      (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.stoppedData s))
                    (And
                      (DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K
                        (@DecrAlmostLinearSSSP.Decremental.State.mk b
                          (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                          (@DecrAlmostLinearSSSP.Decremental.State.y b state)
                          (@DecrAlmostLinearSSSP.Decremental.State.cache b state)
                          (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
                          (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                          (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
                          (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
                          (@DecrAlmostLinearSSSP.Decremental.State.output b state)
                          (@DecrAlmostLinearSSSP.Decremental.State.pending b state) Bool.true
                          (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
                          (@DecrAlmostLinearSSSP.Decremental.State.history b state)))
                      (And
                        (@DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                          (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                          (@DecrAlmostLinearSSSP.Decremental.State.mk b
                            (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                            (@DecrAlmostLinearSSSP.Decremental.State.y b state)
                            (@DecrAlmostLinearSSSP.Decremental.State.cache b state)
                            (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
                            (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                            (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
                            (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
                            (@DecrAlmostLinearSSSP.Decremental.State.output b state)
                            (@DecrAlmostLinearSSSP.Decremental.State.pending b state) Bool.true
                            (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
                            (@DecrAlmostLinearSSSP.Decremental.State.history b state))
                          (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent impl K0 ξ
                              h Γ init (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.stoppedData s) next)))
                        (And
                          (DecrAlmostLinearSSSP.Decremental.RuntimeRepairStep b K state
                            (@DecrAlmostLinearSSSP.Decremental.State.mk b
                              (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                              (@DecrAlmostLinearSSSP.Decremental.State.y b state)
                              (@DecrAlmostLinearSSSP.Decremental.State.cache b state)
                              (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
                              (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                              (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
                              (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
                              (@DecrAlmostLinearSSSP.Decremental.State.output b state)
                              (@DecrAlmostLinearSSSP.Decremental.State.pending b state) Bool.true
                              (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
                              (@DecrAlmostLinearSSSP.Decremental.State.history b state)))
                          (And
                            (@Eq.{1} Nat
                              ((DecrAlmostLinearSSSP.Decremental.CoreNativeCut.stoppedData s).natReg
                                (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))))
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                            (And
                              (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N m exponent impl K0
                                  ξ h Γ init (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.stoppedData s) next)
                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N m exponent impl K0
                                  ξ h Γ init s ctx))
                              (And
                                (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent impl
                                    K0 ξ h Γ init (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.stoppedData s) next)
                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent impl
                                    K0 ξ h Γ init s ctx))
                                (And
                                  (@Eq.{1}
                                    (List.{0}
                                      (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N m exponent impl
                                      K0 ξ h Γ init (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.stoppedData s) next)
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N m exponent impl
                                      K0 ξ h Γ init s ctx))
                                  (@Eq.{1} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N m exponent
                                      impl K0 ξ h Γ init (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.stoppedData s)
                                      next)
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N m exponent
                                      impl K0 ξ h Γ init s ctx)))))))))) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreCommit.headCode
  (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520)))))) ∧ (((∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.refreshCode N p)
    (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520)))) ∧ (∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.drainOneCode N p)
    (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))))) ∧ ((∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.ratioCode N p)
    (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650)))) ∧ ((∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.ratioCode N p)
    (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520)))) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRequest.toggleCode
  (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650)))))))) ∧ ((((DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRequest.toggleCode
  (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520)))) ∧ (∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.toggleCode N p)
    (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))))) ∧ ((∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.toggleCode N p)
    (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520)))) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreNativeCut.stopCode
  (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520)))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.result s)) ∧ (∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.code k)) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 700) (instOfNatNat (nat_lit 700))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.code k) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
        (DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.result s)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
      g (DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.result s))))))) ∧ (((((∀ (K G U : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29)))) G →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))) U →
      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 4)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
              K)) →
        Iff
          ((DecrAlmostLinearSSSP.Decremental.Structured.Test.realLess
                (@OfNat.ofNat.{0} Nat (nat_lit 700) (instOfNatNat (nat_lit 700)))
                (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520)))).holds
            (DecrAlmostLinearSSSP.Decremental.CoreRatioGuard.result s))
          (@LT.lt.{0} Real Real.instLT
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) G U)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 4)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                K)))) ∧ (∀ (N D oldWork newWork calls reports cost : Nat),
  @LE.le.{0} Nat instLENat oldWork newWork →
    @LE.le.{0} Nat instLENat cost
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) D
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) newWork oldWork))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) N))
          (@OfNat.ofNat.{0} Nat (nat_lit 219) (instOfNatNat (nat_lit 219)))) →
      @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (DecrAlmostLinearSSSP.Decremental.CoreRepair.nativeCredit N D oldWork calls reports
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (DecrAlmostLinearSSSP.Decremental.CoreRepair.nativeCredit N D newWork
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) calls
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
          reports (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) ∧ ((∀ (N D oldWork newWork calls reports emitted cost : Nat),
  @LE.le.{0} Nat instLENat oldWork newWork →
    @LE.le.{0} Nat instLENat cost
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) D
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) newWork oldWork))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N))
            (@OfNat.ofNat.{0} Nat (nat_lit 51) (instOfNatNat (nat_lit 51))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) emitted)) →
      @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (DecrAlmostLinearSSSP.Decremental.CoreRepair.nativeCredit N D oldWork calls reports
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (DecrAlmostLinearSSSP.Decremental.CoreRepair.nativeCredit N D newWork
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) calls
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) reports emitted)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) ∧ (∀ (N D oldWork newWork calls reports cost : Nat),
  @LE.le.{0} Nat instLENat oldWork newWork →
    @LE.le.{0} Nat instLENat cost
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) D
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) newWork oldWork))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N))
          (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))) →
      @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (DecrAlmostLinearSSSP.Decremental.CoreRepair.nativeCredit N D oldWork calls reports
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (DecrAlmostLinearSSSP.Decremental.CoreRepair.nativeCredit N D newWork
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) calls
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          reports (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ (((∀ (N D work calls reports : Nat),
  @LE.le.{0} Nat instLENat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (DecrAlmostLinearSSSP.Decremental.CoreRepair.nativeCredit N D work calls reports
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
    (DecrAlmostLinearSSSP.Decremental.CoreRepair.nativeCredit N D work calls reports
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (xs : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
  (calls reports offset : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b s calls reports offset →
    @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
        (@List.cons.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) e xs) →
      DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b (DecrAlmostLinearSSSP.Decremental.refresh b s e)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) calls
          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
        reports offset)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (r : DecrAlmostLinearSSSP.Decremental.CutReply b) (xs : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
  (calls reports emitted offset : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b s calls reports offset →
    @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
        (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
      @LE.le.{0} Nat instLENat (@List.length.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) xs) emitted →
        DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b
          (DecrAlmostLinearSSSP.Decremental.reportedToggle b K s r xs)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) calls
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) reports emitted) offset) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (calls nextCalls reports offset : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b s calls reports offset →
    @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b s) Bool.false →
      @LE.le.{0} Nat instLENat nextCalls
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) calls
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b
          (@DecrAlmostLinearSSSP.Decremental.State.mk b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
            (@DecrAlmostLinearSSSP.Decremental.State.y b s) (@DecrAlmostLinearSSSP.Decremental.State.cache b s)
            (@DecrAlmostLinearSSSP.Decremental.State.baseline b s)
            (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
            (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b s)
            (@DecrAlmostLinearSSSP.Decremental.State.sample b s) (@DecrAlmostLinearSSSP.Decremental.State.output b s)
            (@DecrAlmostLinearSSSP.Decremental.State.pending b s) Bool.true
            (@DecrAlmostLinearSSSP.Decremental.State.toggles b s) (@DecrAlmostLinearSSSP.Decremental.State.history b s))
          nextCalls reports offset) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (before after : DecrAlmostLinearSSSP.Decremental.State b)
  (N D oldWork newWork oldCalls newCalls oldReports newReports oldToggles newToggles cost offset : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreRepair.RatioShape b K before after N D oldWork newWork oldCalls newCalls
      oldReports newReports oldToggles newToggles cost →
    @LE.le.{0} Nat instLENat oldWork newWork →
      @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b before) Bool.false →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b before)
            (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
          DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b before oldCalls oldReports offset →
            @Eq.{1} Nat oldToggles (@DecrAlmostLinearSSSP.Decremental.State.toggles b before) →
              And (DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b after newCalls newReports offset)
                (And (@Eq.{1} Nat newToggles (@DecrAlmostLinearSSSP.Decremental.State.toggles b after))
                  (@LE.le.{0} Nat instLENat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
                        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                      (DecrAlmostLinearSSSP.Decremental.CoreRepair.nativeCredit N D oldWork oldCalls oldReports
                        (@DecrAlmostLinearSSSP.Decremental.CoreRepair.stoppedBit b before)))
                    (DecrAlmostLinearSSSP.Decremental.CoreRepair.nativeCredit N D newWork newCalls newReports
                      (@DecrAlmostLinearSSSP.Decremental.CoreRepair.stoppedBit b after))))))))) ∧ ((((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (ctx :
    DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context b B N
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
      impl K0
      (@HPow.hPow.{0, 0, 0} Real Int Real
        (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))) K
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
      h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
          @LE.le.{0} Real Real.instLE
              (@OfNat.ofNat.{0} Real (nat_lit 32)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
              K →
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K0 →
              @LE.le.{0} Real Real.instLE K0 K →
                DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K state →
                  @DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) state
                      (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                          impl K0
                          (@HPow.hPow.{0, 0, 0} Real Int Real
                            (@instHPow.{0, 0} Real Int
                              (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                            K
                            (@Neg.neg.{0} Int Int.instNegInt
                              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                          h Γ init s ctx)) →
                    @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b state) Bool.false →
                      @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                          (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
                          (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
                        @Ne.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                            (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
                              (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
                                (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero))) →
                          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))))
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))))
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                  (@Neg.neg.{0} Real Real.instNeg
                                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                                    K)) →
                              ∃ cost t after next,
                                And
                                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.ratioDecisionCode N impl.program) s
                                    cost t)
                                  (And (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K after t)
                                    (And (DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K after)
                                      (And
                                        (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                          (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                          (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) after
                                          (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0
                                              (@HPow.hPow.{0, 0, 0} Real Int Real
                                                (@instHPow.{0, 0} Real Int
                                                  (@ZPow.toPow.{0} Real
                                                    (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                K
                                                (@Neg.neg.{0} Int Int.instNegInt
                                                  (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                              h Γ init t next)))
                                        (And (DecrAlmostLinearSSSP.Decremental.RuntimeRepairStep b K state after)
                                          (And
                                            (@Eq.{1} Nat
                                              (t.natReg
                                                (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))))
                                              (@ite.{1} Nat
                                                (@Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b after)
                                                  Bool.true)
                                                (instDecidableEqBool
                                                  (@DecrAlmostLinearSSSP.Decremental.State.stopped b after) Bool.true)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (And
                                              (@Eq.{1} Real
                                                (t.realReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))))
                                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                  (@instHDiv.{0} Real
                                                    (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                  (@Neg.neg.{0} Real Real.instNeg
                                                    (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                      (@One.toOfNat1.{0} Real Real.instOne)))
                                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                                        (@Nat.instAtLeastTwoHAddOfNat
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                                          (@Nat.instNeZeroSucc
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))))))
                                                    K)))
                                              (And
                                                (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      b.input.size)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b.weightExponent)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                    impl K0
                                                    (@HPow.hPow.{0, 0, 0} Real Int Real
                                                      (@instHPow.{0, 0} Real Int
                                                        (@ZPow.toPow.{0} Real
                                                          (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                      K
                                                      (@Neg.neg.{0} Int Int.instNegInt
                                                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                    h Γ init t next)
                                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      b.input.size)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b.weightExponent)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                    impl K0
                                                    (@HPow.hPow.{0, 0, 0} Real Int Real
                                                      (@instHPow.{0, 0} Real Int
                                                        (@ZPow.toPow.{0} Real
                                                          (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                      K
                                                      (@Neg.neg.{0} Int Int.instNegInt
                                                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                    h Γ init s ctx))
                                                (And
                                                  (@LE.le.{0} Nat instLENat
                                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B
                                                        N
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          b.input.size)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b.weightExponent)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                            (instOfNatNat (nat_lit 68))))
                                                        impl K0
                                                        (@HPow.hPow.{0, 0, 0} Real Int Real
                                                          (@instHPow.{0, 0} Real Int
                                                            (@ZPow.toPow.{0} Real
                                                              (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                          K
                                                          (@Neg.neg.{0} Int Int.instNegInt
                                                            (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                              (@instOfNat (nat_lit 2)))))
                                                        h Γ init s ctx).work
                                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B
                                                        N
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          b.input.size)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b.weightExponent)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                            (instOfNatNat (nat_lit 68))))
                                                        impl K0
                                                        (@HPow.hPow.{0, 0, 0} Real Int Real
                                                          (@instHPow.{0, 0} Real Int
                                                            (@ZPow.toPow.{0} Real
                                                              (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                          K
                                                          (@Neg.neg.{0} Int Int.instNegInt
                                                            (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                              (@instOfNat (nat_lit 2)))))
                                                        h Γ init t next).work)
                                                  (DecrAlmostLinearSSSP.Decremental.CoreRepair.RatioShape b K state
                                                    after N
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                                        impl.program.code)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B
                                                        N
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          b.input.size)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b.weightExponent)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                            (instOfNatNat (nat_lit 68))))
                                                        impl K0
                                                        (@HPow.hPow.{0, 0, 0} Real Int Real
                                                          (@instHPow.{0, 0} Real Int
                                                            (@ZPow.toPow.{0} Real
                                                              (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                          K
                                                          (@Neg.neg.{0} Int Int.instNegInt
                                                            (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                              (@instOfNat (nat_lit 2)))))
                                                        h Γ init s ctx).work
                                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B
                                                        N
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          b.input.size)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b.weightExponent)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                            (instOfNatNat (nat_lit 68))))
                                                        impl K0
                                                        (@HPow.hPow.{0, 0, 0} Real Int Real
                                                          (@instHPow.{0, 0} Real Int
                                                            (@ZPow.toPow.{0} Real
                                                              (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                          K
                                                          (@Neg.neg.{0} Int Int.instNegInt
                                                            (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                              (@instOfNat (nat_lit 2)))))
                                                        h Γ init t next).work
                                                    (@List.length.{0}
                                                      (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          b.input.size)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b.weightExponent)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                            (instOfNatNat (nat_lit 68))))
                                                        impl K0
                                                        (@HPow.hPow.{0, 0, 0} Real Int Real
                                                          (@instHPow.{0, 0} Real Int
                                                            (@ZPow.toPow.{0} Real
                                                              (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                          K
                                                          (@Neg.neg.{0} Int Int.instNegInt
                                                            (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                              (@instOfNat (nat_lit 2)))))
                                                        h Γ init s ctx))
                                                    (@List.length.{0}
                                                      (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          b.input.size)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b.weightExponent)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                            (instOfNatNat (nat_lit 68))))
                                                        impl K0
                                                        (@HPow.hPow.{0, 0, 0} Real Int Real
                                                          (@instHPow.{0, 0} Real Int
                                                            (@ZPow.toPow.{0} Real
                                                              (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                          K
                                                          (@Neg.neg.{0} Int Int.instNegInt
                                                            (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                              (@instOfNat (nat_lit 2)))))
                                                        h Γ init t next))
                                                    (DecrAlmostLinearSSSP.Decremental.reportVolume
                                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines
                                                        b B N
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          b.input.size)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b.weightExponent)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                            (instOfNatNat (nat_lit 68))))
                                                        impl K0
                                                        (@HPow.hPow.{0, 0, 0} Real Int Real
                                                          (@instHPow.{0, 0} Real Int
                                                            (@ZPow.toPow.{0} Real
                                                              (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                          K
                                                          (@Neg.neg.{0} Int Int.instNegInt
                                                            (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                              (@instOfNat (nat_lit 2)))))
                                                        h Γ init s ctx))
                                                    (DecrAlmostLinearSSSP.Decremental.reportVolume
                                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines
                                                        b B N
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          b.input.size)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b.weightExponent)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                            (instOfNatNat (nat_lit 68))))
                                                        impl K0
                                                        (@HPow.hPow.{0, 0, 0} Real Int Real
                                                          (@instHPow.{0, 0} Real Int
                                                            (@ZPow.toPow.{0} Real
                                                              (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                          K
                                                          (@Neg.neg.{0} Int Int.instNegInt
                                                            (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                              (@instOfNat (nat_lit 2)))))
                                                        h Γ init t next))
                                                    (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          b.input.size)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b.weightExponent)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                            (instOfNatNat (nat_lit 68))))
                                                        impl K0
                                                        (@HPow.hPow.{0, 0, 0} Real Int Real
                                                          (@instHPow.{0, 0} Real Int
                                                            (@ZPow.toPow.{0} Real
                                                              (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                          K
                                                          (@Neg.neg.{0} Int Int.instNegInt
                                                            (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                              (@instOfNat (nat_lit 2)))))
                                                        h Γ init s ctx))
                                                    (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          b.input.size)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b.weightExponent)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                            (instOfNatNat (nat_lit 68))))
                                                        impl K0
                                                        (@HPow.hPow.{0, 0, 0} Real Int Real
                                                          (@instHPow.{0, 0} Real Int
                                                            (@ZPow.toPow.{0} Real
                                                              (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                          K
                                                          (@Neg.neg.{0} Int Int.instNegInt
                                                            (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                              (@instOfNat (nat_lit 2)))))
                                                        h Γ init t next))
                                                    cost)))))))))) ∧ (∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (ctx :
    DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context b B N
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
      impl K0
      (@HPow.hPow.{0, 0, 0} Real Int Real
        (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))) K
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
      h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
          @LE.le.{0} Real Real.instLE
              (@OfNat.ofNat.{0} Real (nat_lit 32)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
              K →
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K0 →
              @LE.le.{0} Real Real.instLE K0 K →
                DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K state →
                  @DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) state
                      (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                          impl K0
                          (@HPow.hPow.{0, 0, 0} Real Int Real
                            (@instHPow.{0, 0} Real Int
                              (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                            K
                            (@Neg.neg.{0} Int Int.instNegInt
                              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                          h Γ init s ctx)) →
                    @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b state) Bool.false →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@Neg.neg.{0} Real Real.instNeg
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@OfNat.ofNat.{0} Real (nat_lit 4)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                                K)) →
                          ∀ (offset : Nat),
                            DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b state
                                (@List.length.{0}
                                  (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                    impl K0
                                    (@HPow.hPow.{0, 0, 0} Real Int Real
                                      (@instHPow.{0, 0} Real Int
                                        (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                      K
                                      (@Neg.neg.{0} Int Int.instNegInt
                                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                    h Γ init s ctx))
                                (DecrAlmostLinearSSSP.Decremental.reportVolume
                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                    impl K0
                                    (@HPow.hPow.{0, 0, 0} Real Int Real
                                      (@instHPow.{0, 0} Real Int
                                        (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                      K
                                      (@Neg.neg.{0} Int Int.instNegInt
                                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                    h Γ init s ctx))
                                offset →
                              @Eq.{1} Nat
                                  (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                          b.weightExponent)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                      impl K0
                                      (@HPow.hPow.{0, 0, 0} Real Int Real
                                        (@instHPow.{0, 0} Real Int
                                          (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                        K
                                        (@Neg.neg.{0} Int Int.instNegInt
                                          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                      h Γ init s ctx))
                                  (@DecrAlmostLinearSSSP.Decremental.State.toggles b state) →
                                ∃ cost t after next,
                                  And
                                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                      (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.bodyCode N impl.program) s cost t)
                                    (And (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K after t)
                                      (And (DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K after)
                                        (And
                                          (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                            (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) after
                                            (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0
                                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                                  (@instHPow.{0, 0} Real Int
                                                    (@ZPow.toPow.{0} Real
                                                      (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                  K
                                                  (@Neg.neg.{0} Int Int.instNegInt
                                                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                h Γ init t next)))
                                          (And (DecrAlmostLinearSSSP.Decremental.RuntimeRepairStep b K state after)
                                            (And
                                              (@Eq.{1} Nat
                                                (t.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))))
                                                (@ite.{1} Nat
                                                  (@Eq.{1} Bool
                                                    (@DecrAlmostLinearSSSP.Decremental.State.stopped b after) Bool.true)
                                                  (instDecidableEqBool
                                                    (@DecrAlmostLinearSSSP.Decremental.State.stopped b after) Bool.true)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                              (And
                                                (@Eq.{1} Real
                                                  (t.realReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))))
                                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                    (@instHDiv.{0} Real
                                                      (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                    (@Neg.neg.{0} Real Real.instNeg
                                                      (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                        (@One.toOfNat1.{0} Real Real.instOne)))
                                                    (@HMul.hMul.{0, 0, 0} Real Real Real
                                                      (@instHMul.{0} Real Real.instMul)
                                                      (@OfNat.ofNat.{0} Real (nat_lit 4)
                                                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                                          (@Nat.instAtLeastTwoHAddOfNat
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 3)
                                                              (instOfNatNat (nat_lit 3)))
                                                            (@Nat.instNeZeroSucc
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))))))
                                                      K)))
                                                (And
                                                  (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                        b.input.size)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b.weightExponent)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                      impl K0
                                                      (@HPow.hPow.{0, 0, 0} Real Int Real
                                                        (@instHPow.{0, 0} Real Int
                                                          (@ZPow.toPow.{0} Real
                                                            (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                        K
                                                        (@Neg.neg.{0} Int Int.instNegInt
                                                          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                      h Γ init t next)
                                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                        b.input.size)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b.weightExponent)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                      impl K0
                                                      (@HPow.hPow.{0, 0, 0} Real Int Real
                                                        (@instHPow.{0, 0} Real Int
                                                          (@ZPow.toPow.{0} Real
                                                            (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                        K
                                                        (@Neg.neg.{0} Int Int.instNegInt
                                                          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                      h Γ init s ctx))
                                                  (And
                                                    (@LE.le.{0} Nat instLENat
                                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b
                                                          B N
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))
                                                            b.input.size)
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b.weightExponent)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                              (instOfNatNat (nat_lit 68))))
                                                          impl K0
                                                          (@HPow.hPow.{0, 0, 0} Real Int Real
                                                            (@instHPow.{0, 0} Real Int
                                                              (@ZPow.toPow.{0} Real
                                                                (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                            K
                                                            (@Neg.neg.{0} Int Int.instNegInt
                                                              (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                (@instOfNat (nat_lit 2)))))
                                                          h Γ init s ctx).work
                                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b
                                                          B N
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))
                                                            b.input.size)
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b.weightExponent)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                              (instOfNatNat (nat_lit 68))))
                                                          impl K0
                                                          (@HPow.hPow.{0, 0, 0} Real Int Real
                                                            (@instHPow.{0, 0} Real Int
                                                              (@ZPow.toPow.{0} Real
                                                                (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                            K
                                                            (@Neg.neg.{0} Int Int.instNegInt
                                                              (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                (@instOfNat (nat_lit 2)))))
                                                          h Γ init t next).work)
                                                    (And
                                                      (DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b after
                                                        (@List.length.{0}
                                                          (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b
                                                            B N
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              b.input.size)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b.weightExponent)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                (instOfNatNat (nat_lit 68))))
                                                            impl K0
                                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                                              (@instHPow.{0, 0} Real Int
                                                                (@ZPow.toPow.{0} Real
                                                                  (@DivInvMonoid.toZPow.{0} Real
                                                                    Real.instDivInvMonoid)))
                                                              K
                                                              (@Neg.neg.{0} Int Int.instNegInt
                                                                (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                  (@instOfNat (nat_lit 2)))))
                                                            h Γ init t next))
                                                        (DecrAlmostLinearSSSP.Decremental.reportVolume
                                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines
                                                            b B N
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              b.input.size)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b.weightExponent)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                (instOfNatNat (nat_lit 68))))
                                                            impl K0
                                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                                              (@instHPow.{0, 0} Real Int
                                                                (@ZPow.toPow.{0} Real
                                                                  (@DivInvMonoid.toZPow.{0} Real
                                                                    Real.instDivInvMonoid)))
                                                              K
                                                              (@Neg.neg.{0} Int Int.instNegInt
                                                                (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                  (@instOfNat (nat_lit 2)))))
                                                            h Γ init t next))
                                                        offset)
                                                      (And
                                                        (@Eq.{1} Nat
                                                          (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops
                                                              b B N
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                b.input.size)
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                    (instOfNatNat (nat_lit 4)))
                                                                  b.weightExponent)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                  (instOfNatNat (nat_lit 68))))
                                                              impl K0
                                                              (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                (@instHPow.{0, 0} Real Int
                                                                  (@ZPow.toPow.{0} Real
                                                                    (@DivInvMonoid.toZPow.{0} Real
                                                                      Real.instDivInvMonoid)))
                                                                K
                                                                (@Neg.neg.{0} Int Int.instNegInt
                                                                  (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                    (@instOfNat (nat_lit 2)))))
                                                              h Γ init t next))
                                                          (@DecrAlmostLinearSSSP.Decremental.State.toggles b after))
                                                        (And
                                                          (@LE.le.{0} Nat instLENat
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat) cost
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2))))
                                                              (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.credit b N
                                                                impl.program state
                                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current
                                                                  b B N
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                      (instOfNatNat (nat_lit 2)))
                                                                    b.input.size)
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat)
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat)
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                        (instOfNatNat (nat_lit 4)))
                                                                      b.weightExponent)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                      (instOfNatNat (nat_lit 68))))
                                                                  impl K0
                                                                  (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                    (@instHPow.{0, 0} Real Int
                                                                      (@ZPow.toPow.{0} Real
                                                                        (@DivInvMonoid.toZPow.{0} Real
                                                                          Real.instDivInvMonoid)))
                                                                    K
                                                                    (@Neg.neg.{0} Int Int.instNegInt
                                                                      (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                        (@instOfNat (nat_lit 2)))))
                                                                  h Γ init s ctx)
                                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops
                                                                  b B N
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                      (instOfNatNat (nat_lit 2)))
                                                                    b.input.size)
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat)
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat)
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                        (instOfNatNat (nat_lit 4)))
                                                                      b.weightExponent)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                      (instOfNatNat (nat_lit 68))))
                                                                  impl K0
                                                                  (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                    (@instHPow.{0, 0} Real Int
                                                                      (@ZPow.toPow.{0} Real
                                                                        (@DivInvMonoid.toZPow.{0} Real
                                                                          Real.instDivInvMonoid)))
                                                                    K
                                                                    (@Neg.neg.{0} Int Int.instNegInt
                                                                      (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                        (@instOfNat (nat_lit 2)))))
                                                                  h Γ init s ctx)
                                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines
                                                                  b B N
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                      (instOfNatNat (nat_lit 2)))
                                                                    b.input.size)
                                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                    (@instHAdd.{0} Nat instAddNat)
                                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                      (@instHMul.{0} Nat instMulNat)
                                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                        (instOfNatNat (nat_lit 4)))
                                                                      b.weightExponent)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                      (instOfNatNat (nat_lit 68))))
                                                                  impl K0
                                                                  (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                    (@instHPow.{0, 0} Real Int
                                                                      (@ZPow.toPow.{0} Real
                                                                        (@DivInvMonoid.toZPow.{0} Real
                                                                          Real.instDivInvMonoid)))
                                                                    K
                                                                    (@Neg.neg.{0} Int Int.instNegInt
                                                                      (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                        (@instOfNat (nat_lit 2)))))
                                                                  h Γ init s ctx)))
                                                            (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.credit b N
                                                              impl.program after
                                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current
                                                                b B N
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                    (instOfNatNat (nat_lit 2)))
                                                                  b.input.size)
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                      (instOfNatNat (nat_lit 4)))
                                                                    b.weightExponent)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                    (instOfNatNat (nat_lit 68))))
                                                                impl K0
                                                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                  (@instHPow.{0, 0} Real Int
                                                                    (@ZPow.toPow.{0} Real
                                                                      (@DivInvMonoid.toZPow.{0} Real
                                                                        Real.instDivInvMonoid)))
                                                                  K
                                                                  (@Neg.neg.{0} Int Int.instNegInt
                                                                    (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                      (@instOfNat (nat_lit 2)))))
                                                                h Γ init t next)
                                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops
                                                                b B N
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                    (instOfNatNat (nat_lit 2)))
                                                                  b.input.size)
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                      (instOfNatNat (nat_lit 4)))
                                                                    b.weightExponent)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                    (instOfNatNat (nat_lit 68))))
                                                                impl K0
                                                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                  (@instHPow.{0, 0} Real Int
                                                                    (@ZPow.toPow.{0} Real
                                                                      (@DivInvMonoid.toZPow.{0} Real
                                                                        Real.instDivInvMonoid)))
                                                                  K
                                                                  (@Neg.neg.{0} Int Int.instNegInt
                                                                    (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                      (@instOfNat (nat_lit 2)))))
                                                                h Γ init t next)
                                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines
                                                                b B N
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                    (instOfNatNat (nat_lit 2)))
                                                                  b.input.size)
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                      (instOfNatNat (nat_lit 4)))
                                                                    b.weightExponent)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                    (instOfNatNat (nat_lit 68))))
                                                                impl K0
                                                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                  (@instHPow.{0, 0} Real Int
                                                                    (@ZPow.toPow.{0} Real
                                                                      (@DivInvMonoid.toZPow.{0} Real
                                                                        Real.instDivInvMonoid)))
                                                                  K
                                                                  (@Neg.neg.{0} Int Int.instNegInt
                                                                    (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                      (@instOfNat (nat_lit 2)))))
                                                                h Γ init t next)))
                                                          (And
                                                            (@Eq.{1} Bool
                                                                (@DecrAlmostLinearSSSP.Decremental.State.stopped b
                                                                  after)
                                                                Bool.true →
                                                              DecrAlmostLinearSSSP.Decremental.ReadoutCertificate b
                                                                after)
                                                            (@Eq.{1} Bool
                                                                (@DecrAlmostLinearSSSP.Decremental.State.stopped b
                                                                  after)
                                                                Bool.true →
                                                              @Eq.{1}
                                                                (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                                                                (@DecrAlmostLinearSSSP.Decremental.State.pending b
                                                                  after)
                                                                (@List.nil.{0}
                                                                  (DecrAlmostLinearSSSP.Decremental.Edge
                                                                    b))))))))))))))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @WellFounded.{1} (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.Snapshot b)
    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.relation b K)) ∧ ((∀ {σ : Type} (test : DecrAlmostLinearSSSP.Decremental.Structured.Test)
  (body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd)
  (repr : σ → DecrAlmostLinearSSSP.Decremental.Structured.Data → Prop) (rel : σ → σ → Prop),
  @WellFounded.{1} σ rel →
    (∀ (q : σ) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
        repr q s →
          test.holds s →
            ∃ q' t cost,
              And (DecrAlmostLinearSSSP.Decremental.Structured.Eval body s cost t) (And (repr q' t) (rel q' q))) →
      ∀ (q : σ) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
        repr q s →
          ∃ q' t cost,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body) s cost t)
              (And (repr q' t) (Not (test.holds t)))) ∧ (∀ {σ : Type} (test : DecrAlmostLinearSSSP.Decremental.Structured.Test)
  (body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd)
  (repr : σ → DecrAlmostLinearSSSP.Decremental.Structured.Data → Prop) (rel : σ → σ → Prop),
  @WellFounded.{1} σ rel →
    ∀ (budget : σ → Nat),
      (∀ (q : σ) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          repr q s →
            test.holds s →
              ∃ q' t cost,
                And (DecrAlmostLinearSSSP.Decremental.Structured.Eval body s cost t)
                  (And (repr q' t)
                    (And (rel q' q)
                      (@LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (budget q'))
                        (budget q))))) →
        ∀ (q : σ) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          repr q s →
            ∃ q' t cost,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body) s cost t)
                (And (repr q' t)
                  (And (Not (test.holds t))
                    (@LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost (budget q'))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (budget q)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))) ∧ (((∀ {σ : Type} (test : DecrAlmostLinearSSSP.Decremental.Structured.Test)
  (body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd)
  (repr : σ → DecrAlmostLinearSSSP.Decremental.Structured.Data → Prop) (rel : σ → σ → Prop),
  @WellFounded.{1} σ rel →
    ∀ (credit : σ → Nat),
      (∀ (q : σ) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          repr q s →
            test.holds s →
              ∃ q' t cost,
                And (DecrAlmostLinearSSSP.Decremental.Structured.Eval body s cost t)
                  (And (repr q' t)
                    (And (rel q' q)
                      (@LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (credit q))
                        (credit q'))))) →
        ∀ (q : σ) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
          repr q s →
            ∃ q' t cost,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body) s cost t)
                (And (repr q' t)
                  (And (Not (test.holds t))
                    (@LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost (credit q))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (credit q')
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))) ∧ (∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N offset : Nat} {K K0 h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {first : DecrAlmostLinearSSSP.Decremental.Machine}
  {active : Finset.{0} (Fin b.input.k)},
  @LE.le.{0} Nat instLENat b.input.n B →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
      @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
        @LE.le.{0} Real Real.instLE
            (@OfNat.ofNat.{0} Real (nat_lit 32)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
            K →
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K0 →
            @LE.le.{0} Real Real.instLE K0 K →
              DecrAlmostLinearSSSP.Decremental.CutSession impl b.input.n
                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                  first K0
                  (@HPow.hPow.{0, 0, 0} Real Int Real
                    (@instHPow.{0, 0} Real Int
                      (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                    K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                  h Γ init →
                ∀ (q : DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.Snapshot b)
                  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
                  DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.Repr b B N offset K K0 h Γ init impl first
                      active q s →
                    (DecrAlmostLinearSSSP.Decremental.Structured.Test.natLess
                            (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650)))).holds
                        s →
                      ∃ q' t cost,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.bodyCode N impl.program) s cost t)
                          (And
                            (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.Repr b B N offset K K0 h Γ init impl
                              first active q' t)
                            (And (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.relation b K q' q)
                              (@LE.le.{0} Nat instLENat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.credit b N impl.program q))
                                (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.credit b N impl.program q')))))) ∧ ((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N offset : Nat} {K K0 h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {first : DecrAlmostLinearSSSP.Decremental.Machine}
  {active : Finset.{0} (Fin b.input.k)} {q : DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.Snapshot b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.Repr b B N offset K K0 h Γ init impl first active q s →
    Not
        ((DecrAlmostLinearSSSP.Decremental.Structured.Test.natLess
              (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
              (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650)))).holds
          s) →
      @Eq.{1} Bool
        (@DecrAlmostLinearSSSP.Decremental.State.stopped b
          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.Snapshot.state b q))
        Bool.true) ∧ ((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N offset : Nat} {K K0 h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {first : DecrAlmostLinearSSSP.Decremental.Machine}
  {active : Finset.{0} (Fin b.input.k)},
  @LE.le.{0} Nat instLENat b.input.n B →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
      @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
        @LE.le.{0} Real Real.instLE
            (@OfNat.ofNat.{0} Real (nat_lit 32)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
            K →
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K0 →
            @LE.le.{0} Real Real.instLE K0 K →
              DecrAlmostLinearSSSP.Decremental.CutSession impl b.input.n
                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                  first K0
                  (@HPow.hPow.{0, 0, 0} Real Int Real
                    (@instHPow.{0, 0} Real Int
                      (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                    K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                  h Γ init →
                ∀ (q : DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.Snapshot b)
                  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
                  DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.Repr b B N offset K K0 h Γ init impl first
                      active q s →
                    ∃ q' t cost,
                      And
                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                          (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.loopCode N impl.program) s cost t)
                        (And
                          (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.Repr b B N offset K K0 h Γ init impl
                            first active q' t)
                          (And
                            (@Eq.{1} Bool
                              (@DecrAlmostLinearSSSP.Decremental.State.stopped b
                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.Snapshot.state b q'))
                              Bool.true)
                            (And
                              (DecrAlmostLinearSSSP.Decremental.ReadoutCertificate b
                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.Snapshot.state b q'))
                              (@LE.le.{0} Nat instLENat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
                                  (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.credit b N impl.program q))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Repair.credit b N impl.program q')
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRepairControl.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.CoreRepairControl.result s)))))))) ∧ ((((((∀ (K : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512)))) K →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CoreRepairControl.result s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@Eq.{1} Real
        ((DecrAlmostLinearSSSP.Decremental.CoreRepairControl.result s).realReg
          (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 4)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
            K)))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRepairControl.code k)) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 656) (instOfNatNat (nat_lit 656))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 658) (instOfNatNat (nat_lit 658))) →
        DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRepairControl.code k) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreRepairControl.code))) ∧ (((@Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters DecrAlmostLinearSSSP.Decremental.CoreRepairControl.code)
  Bool.true) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
        (DecrAlmostLinearSSSP.Decremental.CoreRepairControl.result s))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
      g (DecrAlmostLinearSSSP.Decremental.CoreRepairControl.result s)) ∧ ((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (ctx :
    DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context b B N
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
      impl K0
      (@HPow.hPow.{0, 0, 0} Real Int Real
        (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))) K
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
      h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
          @LE.le.{0} Real Real.instLE
              (@OfNat.ofNat.{0} Real (nat_lit 32)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
              K →
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K0 →
              @LE.le.{0} Real Real.instLE K0 K →
                DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K state →
                  @DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) state
                      (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                          impl K0
                          (@HPow.hPow.{0, 0, 0} Real Int Real
                            (@instHPow.{0, 0} Real Int
                              (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                            K
                            (@Neg.neg.{0} Int Int.instNegInt
                              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                          h Γ init s ctx)) →
                    @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b state) Bool.false →
                      ∀ (offset : Nat),
                        DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b state
                            (@List.length.{0}
                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                impl K0
                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                  (@instHPow.{0, 0} Real Int
                                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                  K
                                  (@Neg.neg.{0} Int Int.instNegInt
                                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                h Γ init s ctx))
                            (DecrAlmostLinearSSSP.Decremental.reportVolume
                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                impl K0
                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                  (@instHPow.{0, 0} Real Int
                                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                  K
                                  (@Neg.neg.{0} Int Int.instNegInt
                                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                h Γ init s ctx))
                            offset →
                          @Eq.{1} Nat
                              (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                  impl K0
                                  (@HPow.hPow.{0, 0, 0} Real Int Real
                                    (@instHPow.{0, 0} Real Int
                                      (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                    K
                                    (@Neg.neg.{0} Int Int.instNegInt
                                      (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                  h Γ init s ctx))
                              (@DecrAlmostLinearSSSP.Decremental.State.toggles b state) →
                            ∃ cost t after next,
                              And
                                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                  (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.repairCode N impl.program) s cost t)
                                (And (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K after t)
                                  (And (DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K after)
                                    (And
                                      (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                        (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) after
                                        (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              b.input.size)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                b.weightExponent)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                            impl K0
                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                              (@instHPow.{0, 0} Real Int
                                                (@ZPow.toPow.{0} Real
                                                  (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                              K
                                              (@Neg.neg.{0} Int Int.instNegInt
                                                (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                            h Γ init t next)))
                                      (And
                                        (@Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b after)
                                          Bool.true)
                                        (And (DecrAlmostLinearSSSP.Decremental.ReadoutCertificate b after)
                                          (And
                                            (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0
                                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                                  (@instHPow.{0, 0} Real Int
                                                    (@ZPow.toPow.{0} Real
                                                      (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                  K
                                                  (@Neg.neg.{0} Int Int.instNegInt
                                                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                h Γ init t next)
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0
                                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                                  (@instHPow.{0, 0} Real Int
                                                    (@ZPow.toPow.{0} Real
                                                      (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                  K
                                                  (@Neg.neg.{0} Int Int.instNegInt
                                                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                h Γ init s ctx))
                                            (And
                                              (DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b after
                                                (@List.length.{0}
                                                  (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      b.input.size)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b.weightExponent)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                    impl K0
                                                    (@HPow.hPow.{0, 0, 0} Real Int Real
                                                      (@instHPow.{0, 0} Real Int
                                                        (@ZPow.toPow.{0} Real
                                                          (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                      K
                                                      (@Neg.neg.{0} Int Int.instNegInt
                                                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                    h Γ init t next))
                                                (DecrAlmostLinearSSSP.Decremental.reportVolume
                                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B
                                                    N
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      b.input.size)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b.weightExponent)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                    impl K0
                                                    (@HPow.hPow.{0, 0, 0} Real Int Real
                                                      (@instHPow.{0, 0} Real Int
                                                        (@ZPow.toPow.{0} Real
                                                          (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                      K
                                                      (@Neg.neg.{0} Int Int.instNegInt
                                                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                    h Γ init t next))
                                                offset)
                                              (And
                                                (@Eq.{1} Nat
                                                  (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                        b.input.size)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b.weightExponent)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                      impl K0
                                                      (@HPow.hPow.{0, 0, 0} Real Int Real
                                                        (@instHPow.{0, 0} Real Int
                                                          (@ZPow.toPow.{0} Real
                                                            (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                        K
                                                        (@Neg.neg.{0} Int Int.instNegInt
                                                          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                      h Γ init t next))
                                                  (@DecrAlmostLinearSSSP.Decremental.State.toggles b after))
                                                (And
                                                  (@Eq.{1} (Finset.{0} (Fin b.input.k))
                                                    (@DecrAlmostLinearSSSP.Decremental.State.active b after)
                                                    (@DecrAlmostLinearSSSP.Decremental.State.active b state))
                                                  (And
                                                    (@Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                                                      (@DecrAlmostLinearSSSP.Decremental.State.pending b after)
                                                      (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)))
                                                    (@LE.le.{0} Nat instLENat
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        cost
                                                        (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.credit b N
                                                          impl.program state
                                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current
                                                            b B N
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              b.input.size)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b.weightExponent)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                (instOfNatNat (nat_lit 68))))
                                                            impl K0
                                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                                              (@instHPow.{0, 0} Real Int
                                                                (@ZPow.toPow.{0} Real
                                                                  (@DivInvMonoid.toZPow.{0} Real
                                                                    Real.instDivInvMonoid)))
                                                              K
                                                              (@Neg.neg.{0} Int Int.instNegInt
                                                                (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                  (@instOfNat (nat_lit 2)))))
                                                            h Γ init s ctx)
                                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b
                                                            B N
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              b.input.size)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b.weightExponent)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                (instOfNatNat (nat_lit 68))))
                                                            impl K0
                                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                                              (@instHPow.{0, 0} Real Int
                                                                (@ZPow.toPow.{0} Real
                                                                  (@DivInvMonoid.toZPow.{0} Real
                                                                    Real.instDivInvMonoid)))
                                                              K
                                                              (@Neg.neg.{0} Int Int.instNegInt
                                                                (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                  (@instOfNat (nat_lit 2)))))
                                                            h Γ init s ctx)
                                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines
                                                            b B N
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              b.input.size)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b.weightExponent)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                (instOfNatNat (nat_lit 68))))
                                                            impl K0
                                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                                              (@instHPow.{0, 0} Real Int
                                                                (@ZPow.toPow.{0} Real
                                                                  (@DivInvMonoid.toZPow.{0} Real
                                                                    Real.instDivInvMonoid)))
                                                              K
                                                              (@Neg.neg.{0} Int Int.instNegInt
                                                                (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                  (@instOfNat (nat_lit 2)))))
                                                            h Γ init s ctx)))
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.credit b N
                                                          impl.program after
                                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current
                                                            b B N
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              b.input.size)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b.weightExponent)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                (instOfNatNat (nat_lit 68))))
                                                            impl K0
                                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                                              (@instHPow.{0, 0} Real Int
                                                                (@ZPow.toPow.{0} Real
                                                                  (@DivInvMonoid.toZPow.{0} Real
                                                                    Real.instDivInvMonoid)))
                                                              K
                                                              (@Neg.neg.{0} Int Int.instNegInt
                                                                (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                  (@instOfNat (nat_lit 2)))))
                                                            h Γ init t next)
                                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b
                                                            B N
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              b.input.size)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b.weightExponent)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                (instOfNatNat (nat_lit 68))))
                                                            impl K0
                                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                                              (@instHPow.{0, 0} Real Int
                                                                (@ZPow.toPow.{0} Real
                                                                  (@DivInvMonoid.toZPow.{0} Real
                                                                    Real.instDivInvMonoid)))
                                                              K
                                                              (@Neg.neg.{0} Int Int.instNegInt
                                                                (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                  (@instOfNat (nat_lit 2)))))
                                                            h Γ init t next)
                                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines
                                                            b B N
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              b.input.size)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b.weightExponent)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                (instOfNatNat (nat_lit 68))))
                                                            impl K0
                                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                                              (@instHPow.{0, 0} Real Int
                                                                (@ZPow.toPow.{0} Real
                                                                  (@DivInvMonoid.toZPow.{0} Real
                                                                    Real.instDivInvMonoid)))
                                                              K
                                                              (@Neg.neg.{0} Int Int.instNegInt
                                                                (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                  (@instOfNat (nat_lit 2)))))
                                                            h Γ init t next))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 7)
                                                          (instOfNatNat (nat_lit 7)))))))))))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreDeletion.encodeCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (DecrAlmostLinearSSSP.Decremental.CoreDeletion.encoded s)))))) ∧ ((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreDeletion.encodeCode k) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreDeletion.encodeCode k)) ∧ ((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreDeletion.encodeCode) ∧ ((@Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters DecrAlmostLinearSSSP.Decremental.CoreDeletion.encodeCode)
  Bool.true) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
        (DecrAlmostLinearSSSP.Decremental.CoreDeletion.encoded s))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
      g (DecrAlmostLinearSSSP.Decremental.CoreDeletion.encoded s)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (e : Fin b.input.k)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (@Fin.val b.input.k e) →
    @Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.CoreDeletion.encoded s).natReg
        (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
      (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b
        (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : Fin b.input.k) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state s →
    DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B
      (@DecrAlmostLinearSSSP.Decremental.State.mk b
        (@Finset.erase.{0} (Fin b.input.k) (instDecidableEqFin b.input.k)
          (@DecrAlmostLinearSSSP.Decremental.State.active b state) e)
        (@DecrAlmostLinearSSSP.Decremental.State.y b state) (@DecrAlmostLinearSSSP.Decremental.State.cache b state)
        (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
        (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
        (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
        (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
        (@DecrAlmostLinearSSSP.Decremental.State.output b state)
        (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
        (@DecrAlmostLinearSSSP.Decremental.State.stopped b state)
        (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
        (@DecrAlmostLinearSSSP.Decremental.State.history b state))
      { realReg := s.realReg, natReg := s.natReg,
        realMem :=
          @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
            (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B
              (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (DecrAlmostLinearSSSP.Decremental.H b) (DecrAlmostLinearSSSP.Decremental.Q b)),
        natMem := s.natMem }) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : Fin b.input.k) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
        (@DecrAlmostLinearSSSP.Decremental.State.mk b
          (@Finset.erase.{0} (Fin b.input.k) (instDecidableEqFin b.input.k)
            (@DecrAlmostLinearSSSP.Decremental.State.active b state) e)
          (@DecrAlmostLinearSSSP.Decremental.State.y b state) (@DecrAlmostLinearSSSP.Decremental.State.cache b state)
          (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
          (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
          (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
          (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
          (@DecrAlmostLinearSSSP.Decremental.State.output b state)
          (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
          (@DecrAlmostLinearSSSP.Decremental.State.stopped b state)
          (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
          (@DecrAlmostLinearSSSP.Decremental.State.history b state))
        { realReg := s.realReg, natReg := s.natReg,
          realMem :=
            @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
              (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B
                (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (DecrAlmostLinearSSSP.Decremental.H b) (DecrAlmostLinearSSSP.Decremental.Q b)),
          natMem := s.natMem }) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : Fin b.input.k) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
        g s →
      @LE.le.{0} Nat instLENat b.input.n B →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (@Fin.val b.input.k e) →
          ∃ t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreDeletion.headerCode
                s (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) t)
              (And
                (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                  (@DecrAlmostLinearSSSP.Decremental.State.mk b
                    (@Finset.erase.{0} (Fin b.input.k) (instDecidableEqFin b.input.k)
                      (@DecrAlmostLinearSSSP.Decremental.State.active b state) e)
                    (@DecrAlmostLinearSSSP.Decremental.State.y b state)
                    (@DecrAlmostLinearSSSP.Decremental.State.cache b state)
                    (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
                    (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                    (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
                    (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
                    (@DecrAlmostLinearSSSP.Decremental.State.output b state)
                    (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
                    (@DecrAlmostLinearSSSP.Decremental.State.stopped b state)
                    (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
                    (@DecrAlmostLinearSSSP.Decremental.State.history b state))
                  t)
                (And
                  (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g t)
                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b
                      (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e))))))))))) ∧ (((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b) (e : Fin b.input.k),
  @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
      (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
    @Eq.{1} (DecrAlmostLinearSSSP.Decremental.State b)
      (DecrAlmostLinearSSSP.Decremental.refresh b (DecrAlmostLinearSSSP.Decremental.CoreDeletion.pendingState b s e)
        (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e))
      (DecrAlmostLinearSSSP.Decremental.deleteState b s e)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b) (e : Fin b.input.k),
  @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Physical b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b))
    (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b
      (DecrAlmostLinearSSSP.Decremental.CoreDeletion.pendingState b s e)
      (DecrAlmostLinearSSSP.Decremental.logicalCount b) (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
    (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b s (DecrAlmostLinearSSSP.Decremental.logicalCount b)
      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b) (e : Fin b.input.k),
      DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
            (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
          DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K
            (DecrAlmostLinearSSSP.Decremental.refresh b
              (DecrAlmostLinearSSSP.Decremental.CoreDeletion.pendingState b s e)
              (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (e : Fin b.input.k),
  DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
    @DecrAlmostLinearSSSP.Decremental.Physical.Valid b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
      (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b
        (DecrAlmostLinearSSSP.Decremental.CoreDeletion.pendingState b s e)
        (DecrAlmostLinearSSSP.Decremental.logicalCount b) (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b) (e : Fin b.input.k),
      DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
            (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
          DecrAlmostLinearSSSP.Decremental.RefreshValidity b
            (DecrAlmostLinearSSSP.Decremental.CoreDeletion.pendingState b s e)
            (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (ys : List.{0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      (∀ (k : Nat),
          @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
              DecrAlmostLinearSSSP.Decremental.CoreHost.NatRegisters k →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 546) (instOfNatNat (nat_lit 546))) →
              @Eq.{1} Nat (t.natReg k) (s.natReg k)) →
        (∀ (k : Nat),
            @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
                DecrAlmostLinearSSSP.Decremental.CoreHost.RealRegisters k →
              @Eq.{1} Real (t.realReg k) (s.realReg k)) →
          @DecrAlmostLinearSSSP.Decremental.CorePending.View (DecrAlmostLinearSSSP.Decremental.logicalCount b) B ys t →
            @Eq.{1} (Nat → Real) t.realMem s.realMem →
              DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B
                  (DecrAlmostLinearSSSP.Decremental.logicalCount b) s t →
                DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                  (@DecrAlmostLinearSSSP.Decremental.State.mk b (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                    (@DecrAlmostLinearSSSP.Decremental.State.y b state)
                    (@DecrAlmostLinearSSSP.Decremental.State.cache b state)
                    (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
                    (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                    (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
                    (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
                    (@DecrAlmostLinearSSSP.Decremental.State.output b state)
                    (@List.map.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                      (DecrAlmostLinearSSSP.Decremental.Edge b)
                      (@DFunLike.coe.{1, 1, 1}
                        (Equiv.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                          (DecrAlmostLinearSSSP.Decremental.Edge b))
                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                        (fun x => DecrAlmostLinearSSSP.Decremental.Edge b)
                        (@EquivLike.toFunLike.{1, 1, 1}
                          (Equiv.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                            (DecrAlmostLinearSSSP.Decremental.Edge b))
                          (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                          (DecrAlmostLinearSSSP.Decremental.Edge b)
                          (@Equiv.instEquivLike.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                            (DecrAlmostLinearSSSP.Decremental.Edge b)))
                        (@Equiv.symm.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                          (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                          (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)))
                      ys)
                    (@DecrAlmostLinearSSSP.Decremental.State.stopped b state)
                    (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
                    (@DecrAlmostLinearSSSP.Decremental.State.history b state))
                  t)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
        g s →
      @LE.le.{0} Nat instLENat b.input.n B →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
            (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
              (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e) →
            ∃ cost t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CorePending.code s
                  cost t)
                (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
                  (And
                    (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                      (@DecrAlmostLinearSSSP.Decremental.State.mk b
                        (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.y b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.cache b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.output b state)
                        (@List.cons.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) e
                          (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)))
                        (@DecrAlmostLinearSSSP.Decremental.State.stopped b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.history b state))
                      t)
                    (And
                      (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                        (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g t)
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                        (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e)))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : Fin b.input.k) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
        g s →
      @LE.le.{0} Nat instLENat b.input.n B →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
            (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) (@Fin.val b.input.k e) →
            ∃ cost t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  DecrAlmostLinearSSSP.Decremental.CoreDeletion.prepareCode s cost t)
                (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
                  (And
                    (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                      (DecrAlmostLinearSSSP.Decremental.CoreDeletion.pendingState b state e) t)
                    (And
                      (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                        (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g t)
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                        (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b
                          (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e))))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
  (state : DecrAlmostLinearSSSP.Decremental.State b) (e : Fin b.input.k)
  (c : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E state c →
    @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
        (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
        (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
      @DecrAlmostLinearSSSP.Decremental.CutModel b l E
        (DecrAlmostLinearSSSP.Decremental.CoreDeletion.pendingState b state e) c))))) ∧ ((((∀ (N D oldWork newWork calls reports stopped cost : Nat),
  @LE.le.{0} Nat instLENat oldWork newWork →
    @LE.le.{0} Nat instLENat stopped (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @LE.le.{0} Nat instLENat cost
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) D
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) newWork oldWork))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) N))
            (@OfNat.ofNat.{0} Nat (nat_lit 240) (instOfNatNat (nat_lit 240)))) →
        @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
              (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
            (DecrAlmostLinearSSSP.Decremental.CoreRepair.nativeCredit N D oldWork calls reports stopped))
          (DecrAlmostLinearSSSP.Decremental.CoreRepair.nativeCredit N D newWork
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) calls
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
            reports (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b) (e : Fin b.input.k)
  (calls reports offset : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b s calls reports offset →
    @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
        (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
      DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b (DecrAlmostLinearSSSP.Decremental.deleteState b s e)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) calls
          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
        reports
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))) ∧ ((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (ctx :
    DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context b B N
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
      impl K0
      (@HPow.hPow.{0, 0, 0} Real Int Real
        (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))) K
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
      h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
            DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K state →
              @DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) state
                  (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                      impl K0
                      (@HPow.hPow.{0, 0, 0} Real Int Real
                        (@instHPow.{0, 0} Real Int
                          (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                        K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                      h Γ init s ctx)) →
                ∀ (e : Fin b.input.k),
                  @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                      (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
                      (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                        (@Fin.val b.input.k e) →
                      ∀ (offset : Nat),
                        DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b state
                            (@List.length.{0}
                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                impl K0
                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                  (@instHPow.{0, 0} Real Int
                                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                  K
                                  (@Neg.neg.{0} Int Int.instNegInt
                                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                h Γ init s ctx))
                            (DecrAlmostLinearSSSP.Decremental.reportVolume
                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                impl K0
                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                  (@instHPow.{0, 0} Real Int
                                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                  K
                                  (@Neg.neg.{0} Int Int.instNegInt
                                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                h Γ init s ctx))
                            offset →
                          @Eq.{1} Nat
                              (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                  impl K0
                                  (@HPow.hPow.{0, 0, 0} Real Int Real
                                    (@instHPow.{0, 0} Real Int
                                      (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                    K
                                    (@Neg.neg.{0} Int Int.instNegInt
                                      (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                  h Γ init s ctx))
                              (@DecrAlmostLinearSSSP.Decremental.State.toggles b state) →
                            ∃ cost t next,
                              And
                                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                  (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.forcedDeletionCode N impl.program) s
                                  cost t)
                                (And
                                  (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                                    (DecrAlmostLinearSSSP.Decremental.deleteState b state e) t)
                                  (And
                                    (DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K
                                      (DecrAlmostLinearSSSP.Decremental.deleteState b state e))
                                    (And
                                      (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                        (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                                        (DecrAlmostLinearSSSP.Decremental.deleteState b state e)
                                        (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              b.input.size)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                b.weightExponent)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                            impl K0
                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                              (@instHPow.{0, 0} Real Int
                                                (@ZPow.toPow.{0} Real
                                                  (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                              K
                                              (@Neg.neg.{0} Int Int.instNegInt
                                                (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                            h Γ init t next)))
                                      (And
                                        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              b.input.size)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                b.weightExponent)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                            impl K0
                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                              (@instHPow.{0, 0} Real Int
                                                (@ZPow.toPow.{0} Real
                                                  (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                              K
                                              (@Neg.neg.{0} Int Int.instNegInt
                                                (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                            h Γ init t next)
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              b.input.size)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                b.weightExponent)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                            impl K0
                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                              (@instHPow.{0, 0} Real Int
                                                (@ZPow.toPow.{0} Real
                                                  (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                              K
                                              (@Neg.neg.{0} Int Int.instNegInt
                                                (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                            h Γ init s ctx))
                                        (And
                                          (DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b
                                            (DecrAlmostLinearSSSP.Decremental.deleteState b state e)
                                            (@List.length.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0
                                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                                  (@instHPow.{0, 0} Real Int
                                                    (@ZPow.toPow.{0} Real
                                                      (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                  K
                                                  (@Neg.neg.{0} Int Int.instNegInt
                                                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                h Γ init t next))
                                            (DecrAlmostLinearSSSP.Decremental.reportVolume
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0
                                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                                  (@instHPow.{0, 0} Real Int
                                                    (@ZPow.toPow.{0} Real
                                                      (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                  K
                                                  (@Neg.neg.{0} Int Int.instNegInt
                                                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                h Γ init t next))
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                                          (And
                                            (@Eq.{1} Nat
                                              (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    b.input.size)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                      b.weightExponent)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                  impl K0
                                                  (@HPow.hPow.{0, 0, 0} Real Int Real
                                                    (@instHPow.{0, 0} Real Int
                                                      (@ZPow.toPow.{0} Real
                                                        (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                    K
                                                    (@Neg.neg.{0} Int Int.instNegInt
                                                      (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                  h Γ init t next))
                                              (@DecrAlmostLinearSSSP.Decremental.State.toggles b
                                                (DecrAlmostLinearSSSP.Decremental.deleteState b state e)))
                                            (@LE.le.{0} Nat instLENat
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
                                                (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.credit b N impl.program
                                                  state
                                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      b.input.size)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b.weightExponent)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                    impl K0
                                                    (@HPow.hPow.{0, 0, 0} Real Int Real
                                                      (@instHPow.{0, 0} Real Int
                                                        (@ZPow.toPow.{0} Real
                                                          (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                      K
                                                      (@Neg.neg.{0} Int Int.instNegInt
                                                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                    h Γ init s ctx)
                                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      b.input.size)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b.weightExponent)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                    impl K0
                                                    (@HPow.hPow.{0, 0, 0} Real Int Real
                                                      (@instHPow.{0, 0} Real Int
                                                        (@ZPow.toPow.{0} Real
                                                          (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                      K
                                                      (@Neg.neg.{0} Int Int.instNegInt
                                                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                    h Γ init s ctx)
                                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B
                                                    N
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      b.input.size)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b.weightExponent)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                    impl K0
                                                    (@HPow.hPow.{0, 0, 0} Real Int Real
                                                      (@instHPow.{0, 0} Real Int
                                                        (@ZPow.toPow.{0} Real
                                                          (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                      K
                                                      (@Neg.neg.{0} Int Int.instNegInt
                                                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                    h Γ init s ctx)))
                                              (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.credit b N impl.program
                                                (DecrAlmostLinearSSSP.Decremental.deleteState b state e)
                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    b.input.size)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                      b.weightExponent)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                  impl K0
                                                  (@HPow.hPow.{0, 0, 0} Real Int Real
                                                    (@instHPow.{0, 0} Real Int
                                                      (@ZPow.toPow.{0} Real
                                                        (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                    K
                                                    (@Neg.neg.{0} Int Int.instNegInt
                                                      (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                  h Γ init t next)
                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    b.input.size)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                      b.weightExponent)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                  impl K0
                                                  (@HPow.hPow.{0, 0, 0} Real Int Real
                                                    (@instHPow.{0, 0} Real Int
                                                      (@ZPow.toPow.{0} Real
                                                        (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                    K
                                                    (@Neg.neg.{0} Int Int.instNegInt
                                                      (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                  h Γ init t next)
                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    b.input.size)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                      b.weightExponent)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                  impl K0
                                                  (@HPow.hPow.{0, 0, 0} Real Int Real
                                                    (@instHPow.{0, 0} Real Int
                                                      (@ZPow.toPow.{0} Real
                                                        (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                    K
                                                    (@Neg.neg.{0} Int Int.instNegInt
                                                      (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                  h Γ init t next)))))))))) ∧ ((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (ctx :
    DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context b B N
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
      impl K0
      (@HPow.hPow.{0, 0, 0} Real Int Real
        (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))) K
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
      h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
          @LE.le.{0} Real Real.instLE
              (@OfNat.ofNat.{0} Real (nat_lit 32)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
              K →
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K0 →
              @LE.le.{0} Real Real.instLE K0 K →
                DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K state →
                  @DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) state
                      (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                          impl K0
                          (@HPow.hPow.{0, 0, 0} Real Int Real
                            (@instHPow.{0, 0} Real Int
                              (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                            K
                            (@Neg.neg.{0} Int Int.instNegInt
                              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                          h Γ init s ctx)) →
                    ∀ (e : Fin b.input.k),
                      @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                          (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
                          (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                            (@Fin.val b.input.k e) →
                          ∀ (offset : Nat),
                            DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b state
                                (@List.length.{0}
                                  (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                    impl K0
                                    (@HPow.hPow.{0, 0, 0} Real Int Real
                                      (@instHPow.{0, 0} Real Int
                                        (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                      K
                                      (@Neg.neg.{0} Int Int.instNegInt
                                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                    h Γ init s ctx))
                                (DecrAlmostLinearSSSP.Decremental.reportVolume
                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                    impl K0
                                    (@HPow.hPow.{0, 0, 0} Real Int Real
                                      (@instHPow.{0, 0} Real Int
                                        (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                      K
                                      (@Neg.neg.{0} Int Int.instNegInt
                                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                    h Γ init s ctx))
                                offset →
                              @Eq.{1} Nat
                                  (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                          b.weightExponent)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                      impl K0
                                      (@HPow.hPow.{0, 0, 0} Real Int Real
                                        (@instHPow.{0, 0} Real Int
                                          (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                        K
                                        (@Neg.neg.{0} Int Int.instNegInt
                                          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                      h Γ init s ctx))
                                  (@DecrAlmostLinearSSSP.Decremental.State.toggles b state) →
                                ∃ cost t after next,
                                  And
                                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                      (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.updateCode N impl.program) s cost
                                      t)
                                    (And (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K after t)
                                      (And (DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K after)
                                        (And
                                          (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                            (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) after
                                            (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0
                                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                                  (@instHPow.{0, 0} Real Int
                                                    (@ZPow.toPow.{0} Real
                                                      (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                  K
                                                  (@Neg.neg.{0} Int Int.instNegInt
                                                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                h Γ init t next)))
                                          (And
                                            (@Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b after)
                                              Bool.true)
                                            (And (DecrAlmostLinearSSSP.Decremental.ReadoutCertificate b after)
                                              (And
                                                (@Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                                                  (@DecrAlmostLinearSSSP.Decremental.State.pending b after)
                                                  (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)))
                                                (And
                                                  (@Eq.{1} (Finset.{0} (Fin b.input.k))
                                                    (@DecrAlmostLinearSSSP.Decremental.State.active b after)
                                                    (@Finset.erase.{0} (Fin b.input.k) (instDecidableEqFin b.input.k)
                                                      (@DecrAlmostLinearSSSP.Decremental.State.active b state) e))
                                                  (And
                                                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B
                                                        N
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          b.input.size)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b.weightExponent)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                            (instOfNatNat (nat_lit 68))))
                                                        impl K0
                                                        (@HPow.hPow.{0, 0, 0} Real Int Real
                                                          (@instHPow.{0, 0} Real Int
                                                            (@ZPow.toPow.{0} Real
                                                              (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                          K
                                                          (@Neg.neg.{0} Int Int.instNegInt
                                                            (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                              (@instOfNat (nat_lit 2)))))
                                                        h Γ init t next)
                                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B
                                                        N
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          b.input.size)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b.weightExponent)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                            (instOfNatNat (nat_lit 68))))
                                                        impl K0
                                                        (@HPow.hPow.{0, 0, 0} Real Int Real
                                                          (@instHPow.{0, 0} Real Int
                                                            (@ZPow.toPow.{0} Real
                                                              (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                          K
                                                          (@Neg.neg.{0} Int Int.instNegInt
                                                            (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                              (@instOfNat (nat_lit 2)))))
                                                        h Γ init s ctx))
                                                    (And
                                                      (DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b after
                                                        (@List.length.{0}
                                                          (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b
                                                            B N
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              b.input.size)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b.weightExponent)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                (instOfNatNat (nat_lit 68))))
                                                            impl K0
                                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                                              (@instHPow.{0, 0} Real Int
                                                                (@ZPow.toPow.{0} Real
                                                                  (@DivInvMonoid.toZPow.{0} Real
                                                                    Real.instDivInvMonoid)))
                                                              K
                                                              (@Neg.neg.{0} Int Int.instNegInt
                                                                (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                  (@instOfNat (nat_lit 2)))))
                                                            h Γ init t next))
                                                        (DecrAlmostLinearSSSP.Decremental.reportVolume
                                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines
                                                            b B N
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              b.input.size)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b.weightExponent)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                (instOfNatNat (nat_lit 68))))
                                                            impl K0
                                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                                              (@instHPow.{0, 0} Real Int
                                                                (@ZPow.toPow.{0} Real
                                                                  (@DivInvMonoid.toZPow.{0} Real
                                                                    Real.instDivInvMonoid)))
                                                              K
                                                              (@Neg.neg.{0} Int Int.instNegInt
                                                                (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                  (@instOfNat (nat_lit 2)))))
                                                            h Γ init t next))
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          offset
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 6)
                                                            (instOfNatNat (nat_lit 6)))))
                                                      (And
                                                        (@Eq.{1} Nat
                                                          (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops
                                                              b B N
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                b.input.size)
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                    (instOfNatNat (nat_lit 4)))
                                                                  b.weightExponent)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                  (instOfNatNat (nat_lit 68))))
                                                              impl K0
                                                              (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                (@instHPow.{0, 0} Real Int
                                                                  (@ZPow.toPow.{0} Real
                                                                    (@DivInvMonoid.toZPow.{0} Real
                                                                      Real.instDivInvMonoid)))
                                                                K
                                                                (@Neg.neg.{0} Int Int.instNegInt
                                                                  (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                    (@instOfNat (nat_lit 2)))))
                                                              h Γ init t next))
                                                          (@DecrAlmostLinearSSSP.Decremental.State.toggles b after))
                                                        (@LE.le.{0} Nat instLENat
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat) cost
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 7)
                                                                (instOfNatNat (nat_lit 7))))
                                                            (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.credit b N
                                                              impl.program state
                                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current
                                                                b B N
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                    (instOfNatNat (nat_lit 2)))
                                                                  b.input.size)
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                      (instOfNatNat (nat_lit 4)))
                                                                    b.weightExponent)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                    (instOfNatNat (nat_lit 68))))
                                                                impl K0
                                                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                  (@instHPow.{0, 0} Real Int
                                                                    (@ZPow.toPow.{0} Real
                                                                      (@DivInvMonoid.toZPow.{0} Real
                                                                        Real.instDivInvMonoid)))
                                                                  K
                                                                  (@Neg.neg.{0} Int Int.instNegInt
                                                                    (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                      (@instOfNat (nat_lit 2)))))
                                                                h Γ init s ctx)
                                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops
                                                                b B N
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                    (instOfNatNat (nat_lit 2)))
                                                                  b.input.size)
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                      (instOfNatNat (nat_lit 4)))
                                                                    b.weightExponent)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                    (instOfNatNat (nat_lit 68))))
                                                                impl K0
                                                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                  (@instHPow.{0, 0} Real Int
                                                                    (@ZPow.toPow.{0} Real
                                                                      (@DivInvMonoid.toZPow.{0} Real
                                                                        Real.instDivInvMonoid)))
                                                                  K
                                                                  (@Neg.neg.{0} Int Int.instNegInt
                                                                    (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                      (@instOfNat (nat_lit 2)))))
                                                                h Γ init s ctx)
                                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines
                                                                b B N
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                    (instOfNatNat (nat_lit 2)))
                                                                  b.input.size)
                                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                  (@instHAdd.{0} Nat instAddNat)
                                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                    (@instHMul.{0} Nat instMulNat)
                                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                      (instOfNatNat (nat_lit 4)))
                                                                    b.weightExponent)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                    (instOfNatNat (nat_lit 68))))
                                                                impl K0
                                                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                  (@instHPow.{0, 0} Real Int
                                                                    (@ZPow.toPow.{0} Real
                                                                      (@DivInvMonoid.toZPow.{0} Real
                                                                        Real.instDivInvMonoid)))
                                                                  K
                                                                  (@Neg.neg.{0} Int Int.instNegInt
                                                                    (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                      (@instOfNat (nat_lit 2)))))
                                                                h Γ init s ctx)))
                                                          (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.credit b N
                                                            impl.program after
                                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current
                                                              b B N
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                b.input.size)
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                    (instOfNatNat (nat_lit 4)))
                                                                  b.weightExponent)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                  (instOfNatNat (nat_lit 68))))
                                                              impl K0
                                                              (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                (@instHPow.{0, 0} Real Int
                                                                  (@ZPow.toPow.{0} Real
                                                                    (@DivInvMonoid.toZPow.{0} Real
                                                                      Real.instDivInvMonoid)))
                                                                K
                                                                (@Neg.neg.{0} Int Int.instNegInt
                                                                  (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                    (@instOfNat (nat_lit 2)))))
                                                              h Γ init t next)
                                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops
                                                              b B N
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                b.input.size)
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                    (instOfNatNat (nat_lit 4)))
                                                                  b.weightExponent)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                  (instOfNatNat (nat_lit 68))))
                                                              impl K0
                                                              (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                (@instHPow.{0, 0} Real Int
                                                                  (@ZPow.toPow.{0} Real
                                                                    (@DivInvMonoid.toZPow.{0} Real
                                                                      Real.instDivInvMonoid)))
                                                                K
                                                                (@Neg.neg.{0} Int Int.instNegInt
                                                                  (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                    (@instOfNat (nat_lit 2)))))
                                                              h Γ init t next)
                                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines
                                                              b B N
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                b.input.size)
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                    (instOfNatNat (nat_lit 4)))
                                                                  b.weightExponent)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                  (instOfNatNat (nat_lit 68))))
                                                              impl K0
                                                              (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                (@instHPow.{0, 0} Real Int
                                                                  (@ZPow.toPow.{0} Real
                                                                    (@DivInvMonoid.toZPow.{0} Real
                                                                      Real.instDivInvMonoid)))
                                                                K
                                                                (@Neg.neg.{0} Int Int.instNegInt
                                                                  (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                    (@instOfNat (nat_lit 2)))))
                                                              h Γ init t next)))))))))))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.ReadoutCertificate b s →
    ∀ (v : Fin b.input.n),
      @Ne.{1} (Fin b.input.n) v b.input.source →
        ∃ z,
          And
            (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) z)
            (And
              (@Eq.{1} ENNReal
                (DecrAlmostLinearSSSP.Decremental.coreDistance b (@DecrAlmostLinearSSSP.Decremental.State.active b s) v)
                (ENNReal.ofReal z))
              (And
                (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (@DecrAlmostLinearSSSP.Decremental.State.sample b s v))
                (And
                  (@LE.le.{0} Real Real.instLE z
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b.input.accuracy
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
                      (@DecrAlmostLinearSSSP.Decremental.State.sample b s v)))
                  (And
                    (@LE.le.{0} Real Real.instLE
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b.input.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
                        (@DecrAlmostLinearSSSP.Decremental.State.sample b s v))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) b.input.accuracy)
                        z))
                    (And
                      (@LE.le.{0} Real Real.instLE
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@OfNat.ofNat.{0} Real (nat_lit 7)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 7) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))
                            (@OfNat.ofNat.{0} Real (nat_lit 10)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 10) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))
                          z)
                        (@DecrAlmostLinearSSSP.Decremental.State.sample b s v))
                      (@LE.le.{0} Real Real.instLE (@DecrAlmostLinearSSSP.Decremental.State.sample b s v)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@OfNat.ofNat.{0} Real (nat_lit 9)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                            (@OfNat.ofNat.{0} Real (nat_lit 8)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))))
                          z))))))))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.ReadoutCertificate b s →
    ∀ (v : Fin b.input.n),
      @Ne.{1} (Fin b.input.n) v b.input.source →
        @DecrAlmostLinearSSSP.Decremental.Reachable b.input.n b.input.k b.input.graph
            (@DecrAlmostLinearSSSP.Decremental.State.active b s) b.input.source v →
          And
            (@LE.le.{0} ENNReal ENNReal.instLE
              (@DecrAlmostLinearSSSP.Decremental.distance b.input.n b.input.k b.input.graph
                (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                (fun e =>
                  @Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (b.input.weight e))
                b.input.source v)
              (@DecrAlmostLinearSSSP.Decremental.State.output b s v))
            (And
              (@LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.State.output b s v)
                (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                  (@instHMul.{0} ENNReal
                    (@Distrib.toMul.{0} ENNReal
                      (@instDistribOfSemiring.{0} ENNReal
                        (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                  (ENNReal.ofReal
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) b.input.accuracy))
                  (@DecrAlmostLinearSSSP.Decremental.distance b.input.n b.input.k b.input.graph
                    (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                    (fun e =>
                      @Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (b.input.weight e))
                    b.input.source v)))
              (@Ne.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.State.output b s v)
                (@Top.top.{0} ENNReal ENNReal.instTop)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.ReadoutCertificate b s →
    ∀ (v : Fin b.input.n),
      @Ne.{1} (Fin b.input.n) v b.input.source →
        Not
            (@DecrAlmostLinearSSSP.Decremental.Reachable b.input.n b.input.k b.input.graph
              (@DecrAlmostLinearSSSP.Decremental.State.active b s) b.input.source v) →
          @Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.State.output b s v) (@Top.top.{0} ENNReal ENNReal.instTop))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.ReadoutCertificate b s →
    And
      (@Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.State.output b s b.input.source)
        (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
      (∀ (v : Fin b.input.n),
        And
          (@LE.le.{0} ENNReal ENNReal.instLE
            (@DecrAlmostLinearSSSP.Decremental.distance b.input.n b.input.k b.input.graph
              (@DecrAlmostLinearSSSP.Decremental.State.active b s)
              (fun e =>
                @Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  (b.input.weight e))
              b.input.source v)
            (@DecrAlmostLinearSSSP.Decremental.State.output b s v))
          (And
            (@LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.State.output b s v)
              (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                (@instHMul.{0} ENNReal
                  (@Distrib.toMul.{0} ENNReal
                    (@instDistribOfSemiring.{0} ENNReal
                      (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                (ENNReal.ofReal
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) b.input.accuracy))
                (@DecrAlmostLinearSSSP.Decremental.distance b.input.n b.input.k b.input.graph
                  (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                  (fun e =>
                    @Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (b.input.weight e))
                  b.input.source v)))
            (Iff
              (@Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.State.output b s v)
                (@Top.top.{0} ENNReal ENNReal.instTop))
              (Not
                (@DecrAlmostLinearSSSP.Decremental.Reachable b.input.n b.input.k b.input.graph
                  (@DecrAlmostLinearSSSP.Decremental.State.active b s) b.input.source v)))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.ReadoutCertificate b state →
      And
        (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val b.input.n b.input.source))
          (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
        (And
          (∀ (v : Fin b.input.n),
            And
              (@LE.le.{0} Nat instLENat (s.natMem (@Fin.val b.input.n v))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Eq.{1} Nat (s.natMem (@Fin.val b.input.n v))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  (s.realMem (@Fin.val b.input.n v))))
          (∀ (v : Fin b.input.n),
            And
              (@LE.le.{0} ENNReal ENNReal.instLE
                (@DecrAlmostLinearSSSP.Decremental.distance b.input.n b.input.k b.input.graph
                  (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                  (fun e =>
                    @Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (b.input.weight e))
                  b.input.source v)
                (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val b.input.n v)))
              (And
                (@LE.le.{0} ENNReal ENNReal.instLE
                  (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val b.input.n v))
                  (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                    (@instHMul.{0} ENNReal
                      (@Distrib.toMul.{0} ENNReal
                        (@instDistribOfSemiring.{0} ENNReal
                          (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                    (ENNReal.ofReal
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) b.input.accuracy))
                    (@DecrAlmostLinearSSSP.Decremental.distance b.input.n b.input.k b.input.graph
                      (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                      (fun e =>
                        @Nat.cast.{0} ENNReal
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          (b.input.weight e))
                      b.input.source v)))
                (Iff
                  (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val b.input.n v))
                    (@Top.top.{0} ENNReal ENNReal.instTop))
                  (Not
                    (@DecrAlmostLinearSSSP.Decremental.Reachable b.input.n b.input.k b.input.graph
                      (@DecrAlmostLinearSSSP.Decremental.State.active b state) b.input.source v))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CutQualityNative.rootPower s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.CutQualityNative.powered s))))))))) := by sorry
