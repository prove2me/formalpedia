-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_9
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T17:33:20.713751+00:00
-- url     : https://prove2.me/theorems/3bbdd98a-22cd-466d-920a-5d1a71e386cf
-- title:
--   Native label queries, physical refresh and queues
-- statement:
--   Let the graph, labels, caches, cut states and scalar RAM machines be the objects of the normalized decremental SSSP implementation interface. Each component below is universally quantified over its own parameters and representation hypotheses.
--
--   Native label queries and physical refresh calls return the current endpoint labels, capacities and physical cut state. Queue and host-memory operations preserve the appropriate geometry, gradient, historical samples and public entries. The representation and frame contracts justify composing these concrete operations during a cache refresh.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_9 : (((((((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N m exponent : Nat} {K K0 ξ h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (ctx : DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context b B N m exponent impl K0 ξ h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
          @DecrAlmostLinearSSSP.Decremental.Physical.Valid b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
              (@DecrAlmostLinearSSSP.Decremental.CutState.physical b.input.n
                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent impl K0 ξ h Γ init s
                    ctx)))
              m exponent →
            @DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) state
                (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent impl K0 ξ h Γ init s
                    ctx)) →
              ∀ (a z : Fin b.input.n),
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 636) (instOfNatNat (nat_lit 636))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val b.input.n a)) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 638) (instOfNatNat (nat_lit 638))))
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val b.input.n z)) →
                    ∃ cost t next,
                      And
                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                          (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.labelsCode N impl.program) s cost t)
                        (And
                          (@LE.le.{0} Nat instLENat cost
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent
                                        impl K0 ξ h Γ init t next).work
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent
                                        impl K0 ξ h Γ init s ctx).work))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))) N))
                              (@OfNat.ofNat.{0} Nat (nat_lit 46) (instOfNatNat (nat_lit 46)))))
                          (And (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t)
                            (And
                              (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) state
                                (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent impl
                                    K0 ξ h Γ init t next)))
                              (And
                                (@Eq.{1} Real
                                  (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))))
                                  (@DecrAlmostLinearSSSP.Decremental.State.y b state a))
                                (And
                                  (@Eq.{1} Real
                                    (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))
                                    (@DecrAlmostLinearSSSP.Decremental.State.y b state z))
                                  (And
                                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N m exponent
                                        impl K0 ξ h Γ init t next)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N m exponent
                                        impl K0 ξ h Γ init s ctx))
                                    (And
                                      (@Eq.{1}
                                        (List.{0}
                                          (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N m exponent
                                          impl K0 ξ h Γ init t next)
                                        (@HAppend.hAppend.{0, 0, 0}
                                          (List.{0}
                                            (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                          (List.{0}
                                            (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                          (List.{0}
                                            (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                          (@instHAppendOfAppend.{0}
                                            (List.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                            (@List.instAppend.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N m exponent
                                            impl K0 ξ h Γ init s ctx)
                                          (@List.cons.{0}
                                            (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                            (@DecrAlmostLinearSSSP.Decremental.CutOp.queryY b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b) a)
                                            (@List.cons.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                              (@DecrAlmostLinearSSSP.Decremental.CutOp.queryY b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b) z)
                                              (@List.nil.{0}
                                                (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)))))))
                                      (And
                                        (∃ middle,
                                          @Eq.{1} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N m
                                              exponent impl K0 ξ h Γ init t next)
                                            (@HAppend.hAppend.{0, 0, 0}
                                              (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                              (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                              (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                              (@instHAppendOfAppend.{0}
                                                (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                                (@List.instAppend.{0} DecrAlmostLinearSSSP.Decremental.Machine))
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N m
                                                exponent impl K0 ξ h Γ init s ctx)
                                              (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Machine middle
                                                (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Machine
                                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                    m exponent impl K0 ξ h Γ init t next)
                                                  (@List.nil.{0} DecrAlmostLinearSSSP.Decremental.Machine)))))
                                        (And
                                          (@LE.le.{0} Nat instLENat
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                                exponent impl K0 ξ h Γ init s ctx).work
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                                exponent impl K0 ξ h Γ init t next).work)
                                          (@Eq.{1} Nat
                                            (DecrAlmostLinearSSSP.Decremental.reportVolume
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N m
                                                exponent impl K0 ξ h Γ init t next))
                                            (DecrAlmostLinearSSSP.Decremental.reportVolume
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N m
                                                exponent impl K0 ξ h Γ init s ctx))))))))))))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 636) (instOfNatNat (nat_lit 636))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 638) (instOfNatNat (nat_lit 638))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRequest.insertCode k)) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 636) (instOfNatNat (nat_lit 636))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 638) (instOfNatNat (nat_lit 638))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRequest.pairedCode k) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRequest.insertCode k))) ∧ (((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRequest.pairedCode k) ∧ (∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.eraseCode N p) k)) ∧ ((∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 636) (instOfNatNat (nat_lit 636))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 638) (instOfNatNat (nat_lit 638))) →
                  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.insertCode N p) k) ∧ ((∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 636) (instOfNatNat (nat_lit 636))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 638) (instOfNatNat (nat_lit 638))) →
                  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.pairedCode N p) k) ∧ (∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
        (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.eraseCode N p) k))))) ∧ ((((∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
        (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.insertCode N p) k) ∧ (∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
        (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.pairedCode N p) k)) ∧ ((∀ {n k : Nat} (a b : DecrAlmostLinearSSSP.Decremental.Physical n k),
  @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Digraph n k) (@DecrAlmostLinearSSSP.Decremental.Physical.graph n k a)
      (@DecrAlmostLinearSSSP.Decremental.Physical.graph n k b) →
    @Eq.{1} (Finset.{0} (Fin k)) (@DecrAlmostLinearSSSP.Decremental.Physical.active n k a)
        (@DecrAlmostLinearSSSP.Decremental.Physical.active n k b) →
      @Eq.{1} (Fin k → Real) (@DecrAlmostLinearSSSP.Decremental.Physical.u n k a)
          (@DecrAlmostLinearSSSP.Decremental.Physical.u n k b) →
        @Eq.{1} (Fin n → Real) (@DecrAlmostLinearSSSP.Decremental.Physical.gamma n k a)
            (@DecrAlmostLinearSSSP.Decremental.Physical.gamma n k b) →
          @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Physical n k) a b) ∧ (∀ {n k m exponent : Nat} (h : DecrAlmostLinearSSSP.Decremental.Physical n k),
  @DecrAlmostLinearSSSP.Decremental.Physical.Valid n k h m exponent →
    ∀ (e : Fin k),
      (∀ (x : Fin n → Real),
          @Eq.{1} Real
              (@DecrAlmostLinearSSSP.Decremental.physicalNorm n k
                (@DecrAlmostLinearSSSP.Decremental.applyPhysical n k h
                  (@DecrAlmostLinearSSSP.Decremental.CutOp.erase n k e))
                x)
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
            ∀ (v w : Fin n), @Eq.{1} Real (x v) (x w)) →
        @DecrAlmostLinearSSSP.Decremental.Physical.Valid n k
          (@DecrAlmostLinearSSSP.Decremental.applyPhysical n k h (@DecrAlmostLinearSSSP.Decremental.CutOp.erase n k e))
          m exponent))) ∧ (((∀ {n k m exponent : Nat} (h : DecrAlmostLinearSSSP.Decremental.Physical n k),
  @DecrAlmostLinearSSSP.Decremental.Physical.Valid n k h m exponent →
    ∀ (g : Fin n → Real),
      @Eq.{1} Real (∑ v, g v) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        (∀ (v : Fin n),
            @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup (g v))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@Max.max.{0} Real Real.instMax
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (@Nat.cast.{0} Real Real.instNatCast m))
                exponent)) →
          @DecrAlmostLinearSSSP.Decremental.Physical.Valid n k
            (@DecrAlmostLinearSSSP.Decremental.Physical.mk n k (@DecrAlmostLinearSSSP.Decremental.Physical.graph n k h)
              (@DecrAlmostLinearSSSP.Decremental.Physical.active n k h)
              (@DecrAlmostLinearSSSP.Decremental.Physical.u n k h) g)
            m exponent) ∧ (∀ {n k : Nat} (h : DecrAlmostLinearSSSP.Decremental.Physical n k) (e : Fin k) (cap : Real),
  @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
      (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k)))
      (@DecrAlmostLinearSSSP.Decremental.Physical.active n k h) e →
    @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Physical n k)
      (@DecrAlmostLinearSSSP.Decremental.applyPhysical n k
        (@DecrAlmostLinearSSSP.Decremental.applyPhysical n k h (@DecrAlmostLinearSSSP.Decremental.CutOp.erase n k e))
        (@DecrAlmostLinearSSSP.Decremental.CutOp.insert n k e
          (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k (@DecrAlmostLinearSSSP.Decremental.Physical.graph n k h)
            e)
          (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k (@DecrAlmostLinearSSSP.Decremental.Physical.graph n k h)
            e)
          cap))
      (@DecrAlmostLinearSSSP.Decremental.Physical.mk n k (@DecrAlmostLinearSSSP.Decremental.Physical.graph n k h)
        (@DecrAlmostLinearSSSP.Decremental.Physical.active n k h)
        (@Function.update.{1, 1} (Fin k) (fun a => Real) (instDecidableEqFin k)
          (@DecrAlmostLinearSSSP.Decremental.Physical.u n k h) e cap)
        (@DecrAlmostLinearSSSP.Decremental.Physical.gamma n k h)))) ∧ ((∀ {n k : Nat} (h : DecrAlmostLinearSSSP.Decremental.Physical n k),
  (∀ (e : Fin k),
      @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
          (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k)))
          (@DecrAlmostLinearSSSP.Decremental.Physical.active n k h) e →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@DecrAlmostLinearSSSP.Decremental.Physical.u n k h e)) →
    ∀ (x : Fin n → Real),
      @Eq.{1} Real (@DecrAlmostLinearSSSP.Decremental.physicalNorm n k h x)
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        ∀ (e : Fin k),
          @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
              (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k)))
              (@DecrAlmostLinearSSSP.Decremental.Physical.active n k h) e →
            @Eq.{1} Real
              (x
                (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k
                  (@DecrAlmostLinearSSSP.Decremental.Physical.graph n k h) e))
              (x
                (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k
                  (@DecrAlmostLinearSSSP.Decremental.Physical.graph n k h) e))) ∧ ((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    ∀ (e : Fin k),
      @Membership.mem.{0, 0} (Fin k) (List.{0} (Fin k)) (@List.instMembership.{0} (Fin k)) es e →
        @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
          (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active e) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    ∀ (x : Fin n → Real),
      (∀ (e : Fin k),
          @Membership.mem.{0, 0} (Fin k) (List.{0} (Fin k)) (@List.instMembership.{0} (Fin k)) es e →
            @Eq.{1} Real (x (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e))
              (x (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e))) →
        @Eq.{1} Real (x u) (x v))))))) ∧ (((((∀ {n k : Nat} (h : DecrAlmostLinearSSSP.Decremental.Physical n k),
  (∀ (e : Fin k),
      @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
          (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k)))
          (@DecrAlmostLinearSSSP.Decremental.Physical.active n k h) e →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@DecrAlmostLinearSSSP.Decremental.Physical.u n k h e)) →
    ∀ (s : Fin n),
      (∀ (v : Fin n),
          ∃ es,
            @DecrAlmostLinearSSSP.Decremental.Walk n k (@DecrAlmostLinearSSSP.Decremental.Physical.graph n k h)
              (@DecrAlmostLinearSSSP.Decremental.Physical.active n k h) s v es) →
        ∀ (x : Fin n → Real),
          @Eq.{1} Real (@DecrAlmostLinearSSSP.Decremental.physicalNorm n k h x)
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
            ∀ (v w : Fin n), @Eq.{1} Real (x v) (x w)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b),
  (∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@DecrAlmostLinearSSSP.Decremental.State.cache b s e)) →
    ∀ (x : Fin b.input.n → Real),
      @Eq.{1} Real
          (@DecrAlmostLinearSSSP.Decremental.physicalNorm b.input.n
            (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
              (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
            (DecrAlmostLinearSSSP.Decremental.cachedPhysical b s) x)
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        ∀ (v w : Fin b.input.n), @Eq.{1} Real (x v) (x w))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b),
  (∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@DecrAlmostLinearSSSP.Decremental.State.cache b s e)) →
    ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b) (x : Fin b.input.n → Real),
      @Eq.{1} Real
          (@DecrAlmostLinearSSSP.Decremental.physicalNorm b.input.n
            (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
              (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
            (@DecrAlmostLinearSSSP.Decremental.applyPhysical b.input.n
              (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                  (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
              (DecrAlmostLinearSSSP.Decremental.cachedPhysical b s)
              (@DecrAlmostLinearSSSP.Decremental.CutOp.erase b.input.n
                (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                  (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                    (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
                (@DFunLike.coe.{1, 1, 1}
                  (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                    (Fin
                      (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                        (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                          (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))))
                  (DecrAlmostLinearSSSP.Decremental.Edge b)
                  (fun x =>
                    Fin
                      (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                        (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                          (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b))))
                  (@EquivLike.toFunLike.{1, 1, 1}
                    (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                      (Fin
                        (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                          (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                            (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))))
                    (DecrAlmostLinearSSSP.Decremental.Edge b)
                    (Fin
                      (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                        (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                          (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b))))
                    (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                      (Fin
                        (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                          (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                            (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b))))))
                  (@Fintype.equivFin.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                    (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                      (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
                  e)))
            x)
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        ∀ (v w : Fin b.input.n), @Eq.{1} Real (x v) (x w)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (p : Fin b.input.n → Real)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  ∃ es,
    And (@LE.le.{0} Nat instLENat (@List.length.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) es) b.input.n)
      (@LE.le.{0} Real Real.instLE
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@List.sum.{0} Real Real.instAdd Real.instZero
            (@List.map.{0, 0} (DecrAlmostLinearSSSP.Decremental.Edge b) Real
              (DecrAlmostLinearSSSP.Decremental.slack b active p) es))
          (DecrAlmostLinearSSSP.Decremental.slack b active p e))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 8)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))))) ∧ (((∀ {κ t L : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) κ →
    @LE.le.{0} Real Real.instLE κ L →
      @LE.le.{0} Real Real.instLE t L →
        @LE.le.{0} Real Real.instLE (@Neg.neg.{0} Real Real.instNeg (Real.log L))
          (DecrAlmostLinearSSSP.Decremental.clippedLog κ t)) ∧ (∀ {κ t : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) κ →
    @LE.le.{0} Real Real.instLE κ (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      @LE.le.{0} Real Real.instLE t (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (DecrAlmostLinearSSSP.Decremental.clippedLog κ t))) ∧ ((∀ {κ t L N : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) κ →
    @LE.le.{0} Real Real.instLE κ (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) L →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) N →
          @LT.lt.{0} Real Real.instLT t
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@Neg.neg.{0} Real Real.instNeg L)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  N)) →
            @LE.le.{0} Real Real.instLE
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) L
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    N)
                  κ))
              (DecrAlmostLinearSSSP.Decremental.clippedLog κ t)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (p : Fin b.input.n → Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (DecrAlmostLinearSSSP.Decremental.potential b active p)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (p : Fin b.input.n → Real)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (DecrAlmostLinearSSSP.Decremental.slack b active p e) →
    (∀ (d : DecrAlmostLinearSSSP.Decremental.Edge b),
        @LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.slack b active p d)
          (DecrAlmostLinearSSSP.Decremental.slack b active p e)) →
      @LE.le.{0} Real Real.instLE
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (DecrAlmostLinearSSSP.Decremental.slack b active p e)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (@Nat.cast.{0} Real Real.instNatCast b.input.n))
              (DecrAlmostLinearSSSP.Decremental.kappa b)))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (∑ d, DecrAlmostLinearSSSP.Decremental.coefficient b d)
            (Real.log (DecrAlmostLinearSSSP.Decremental.slack b active p e))))
        (DecrAlmostLinearSSSP.Decremental.potential b active p)))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 8)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
            (@Nat.cast.{0} Real Real.instNatCast b.input.n))
          (DecrAlmostLinearSSSP.Decremental.A b))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@Nat.cast.{0} Real Real.instNatCast b.input.size)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (DecrAlmostLinearSSSP.Decremental.kappa b))
    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LT.lt.{0} Real Real.instLT
    (DecrAlmostLinearSSSP.Decremental.potential b (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
      (DecrAlmostLinearSSSP.Decremental.initialLabel b))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
          (@Nat.cast.{0} Real Real.instNatCast b.input.n))
        (DecrAlmostLinearSSSP.Decremental.kappa b))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (p : Fin b.input.n → Real),
  @LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.potential b active p)
      (DecrAlmostLinearSSSP.Decremental.potential b (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
        (DecrAlmostLinearSSSP.Decremental.initialLabel b)) →
    ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
      @LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.slack b active p e)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (p : Fin b.input.n → Real),
  (∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
      @LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.slack b active p e)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
    ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (DecrAlmostLinearSSSP.Decremental.capacity b active p e)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  @LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.cacheModel b s e)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (DecrAlmostLinearSSSP.Decremental.A b)
        (@Nat.cast.{0} Real Real.instNatCast b.input.size))
      (DecrAlmostLinearSSSP.Decremental.kappa b)))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
        @LE.le.{0} Real Real.instLE
          (DecrAlmostLinearSSSP.Decremental.potential b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
            (DecrAlmostLinearSSSP.Decremental.labels b s))
          (DecrAlmostLinearSSSP.Decremental.potential b (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
            (DecrAlmostLinearSSSP.Decremental.initialLabel b))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K (DecrAlmostLinearSSSP.Decremental.initializeState b))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
        ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
          DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K (DecrAlmostLinearSSSP.Decremental.refresh b s e)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
        ∀ (e : Fin b.input.k),
          DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K (DecrAlmostLinearSSSP.Decremental.deleteState b s e)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
            (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
          ∀ (r : DecrAlmostLinearSSSP.Decremental.CutReply b),
            @DecrAlmostLinearSSSP.Decremental.RatioGuarantee b.input.n
                (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                  (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                    (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
                (DecrAlmostLinearSSSP.Decremental.cachedPhysical b s) K
                (@DecrAlmostLinearSSSP.Decremental.CutReply.G b r) (@DecrAlmostLinearSSSP.Decremental.CutReply.U b r)
                (@DecrAlmostLinearSSSP.Decremental.CutReply.cut b r) →
              @LT.lt.{0} Real Real.instLT
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@DecrAlmostLinearSSSP.Decremental.CutReply.G b r)
                    (@DecrAlmostLinearSSSP.Decremental.CutReply.U b r))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Neg.neg.{0} Real Real.instNeg
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 4)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      K)) →
                ∀ (reports : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)),
                  DecrAlmostLinearSSSP.Decremental.ReportsComplete b K s r reports →
                    DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K
                      (DecrAlmostLinearSSSP.Decremental.reportedToggle b K s r reports)))))))) ∧ ((((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Nat instLENat
    (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
      (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) (Fin.fintype b.input.k)
        (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (f : DecrAlmostLinearSSSP.Decremental.Edge b → Real),
  @Eq.{1} Real (∑ v, DecrAlmostLinearSSSP.Decremental.gradient b f v)
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (f : DecrAlmostLinearSSSP.Decremental.Edge b → Real),
  (∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (f e)) →
    ∀ (v : Fin b.input.n),
      @LE.le.{0} Real Real.instLE
        (@abs.{0} Real Real.lattice Real.instAddGroup (DecrAlmostLinearSSSP.Decremental.gradient b f v)) (∑ e, f e)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
    @LE.le.{0} Real Real.instLE (∑ e, @DecrAlmostLinearSSSP.Decremental.State.cache b s e)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (DecrAlmostLinearSSSP.Decremental.A b))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@Nat.cast.{0} Real Real.instNatCast b.input.size)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (DecrAlmostLinearSSSP.Decremental.kappa b))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (DecrAlmostLinearSSSP.Decremental.A b))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@Nat.cast.{0} Real Real.instNatCast b.input.size)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (DecrAlmostLinearSSSP.Decremental.kappa b))
    (@HPow.hPow.{0, 0, 0} Real Int Real
      (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
      (DecrAlmostLinearSSSP.Decremental.kappa b)
      (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.A b)
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@Nat.cast.{0} Real Real.instNatCast b.input.size) (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.Q b)
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@Nat.cast.{0} Real Real.instNatCast b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.weightExponent
        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE
    (@HPow.hPow.{0, 0, 0} Real Int Real
      (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
      (DecrAlmostLinearSSSP.Decremental.kappa b)
      (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@Nat.cast.{0} Real Real.instNatCast b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  And
    (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@HPow.hPow.{0, 0, 0} Real Int Real
        (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
        (DecrAlmostLinearSSSP.Decremental.kappa b)
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
    (@LE.le.{0} Real Real.instLE
      (@HPow.hPow.{0, 0, 0} Real Int Real
        (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
        (DecrAlmostLinearSSSP.Decremental.kappa b)
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (@Max.max.{0} Real Real.instMax
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (@Nat.cast.{0} Real Real.instNatCast b.input.size)))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
          (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))))))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
    @DecrAlmostLinearSSSP.Decremental.Physical.Valid b.input.n
      (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
        (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
          (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
      (DecrAlmostLinearSSSP.Decremental.cachedPhysical b s)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
    ∀ {l : Nat} (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)),
      @LE.le.{0} Nat instLENat l
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size) →
        @DecrAlmostLinearSSSP.Decremental.Physical.Valid b.input.n l
          (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b s l E)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b),
  (∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@DecrAlmostLinearSSSP.Decremental.State.cache b s e)) →
    ∀ {l : Nat} (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
      (e : DecrAlmostLinearSSSP.Decremental.Edge b) (x : Fin b.input.n → Real),
      @Eq.{1} Real
          (@DecrAlmostLinearSSSP.Decremental.physicalNorm b.input.n l
            (@DecrAlmostLinearSSSP.Decremental.applyPhysical b.input.n l
              (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b s l E)
              (@DecrAlmostLinearSSSP.Decremental.CutOp.erase b.input.n l
                (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                  (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
                  (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                    (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
                    (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
                  E e)))
            x)
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        ∀ (v w : Fin b.input.n), @Eq.{1} Real (x v) (x w)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Physical b.input.n l)
    (have __src := @DecrAlmostLinearSSSP.Decremental.indexedPhysical b s l E;
    @DecrAlmostLinearSSSP.Decremental.Physical.mk b.input.n l
      (@DecrAlmostLinearSSSP.Decremental.Physical.graph b.input.n l __src)
      (@DecrAlmostLinearSSSP.Decremental.Physical.active b.input.n l __src)
      (@Function.update.{1, 1} (Fin l) (fun a => Real) (instDecidableEqFin l)
        (@DecrAlmostLinearSSSP.Decremental.Physical.u b.input.n l
          (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b s l E))
        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
          (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
          (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
            (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
            (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
          E e)
        (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
          (DecrAlmostLinearSSSP.Decremental.labels b s) e))
      (@DecrAlmostLinearSSSP.Decremental.Physical.gamma b.input.n l __src))
    (have __src :=
      @DecrAlmostLinearSSSP.Decremental.indexedPhysical b (DecrAlmostLinearSSSP.Decremental.refresh b s e) l E;
    @DecrAlmostLinearSSSP.Decremental.Physical.mk b.input.n l
      (@DecrAlmostLinearSSSP.Decremental.Physical.graph b.input.n l __src)
      (@DecrAlmostLinearSSSP.Decremental.Physical.active b.input.n l __src)
      (@DecrAlmostLinearSSSP.Decremental.Physical.u b.input.n l __src)
      (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Physical b.input.n l)
    (@DecrAlmostLinearSSSP.Decremental.applyPhysical b.input.n l
      (@DecrAlmostLinearSSSP.Decremental.applyPhysical b.input.n l
        (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b s l E)
        (@DecrAlmostLinearSSSP.Decremental.CutOp.erase b.input.n l
          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
            (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
              (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
              (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
            E e)))
      (@DecrAlmostLinearSSSP.Decremental.CutOp.insert b.input.n l
        (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
          (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
          (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
            (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
            (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
          E e)
        (DecrAlmostLinearSSSP.Decremental.tail b e) (DecrAlmostLinearSSSP.Decremental.head b e)
        (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
          (DecrAlmostLinearSSSP.Decremental.labels b s) e)))
    (have __src :=
      @DecrAlmostLinearSSSP.Decremental.indexedPhysical b (DecrAlmostLinearSSSP.Decremental.refresh b s e) l E;
    @DecrAlmostLinearSSSP.Decremental.Physical.mk b.input.n l
      (@DecrAlmostLinearSSSP.Decremental.Physical.graph b.input.n l __src)
      (@DecrAlmostLinearSSSP.Decremental.Physical.active b.input.n l __src)
      (@DecrAlmostLinearSSSP.Decremental.Physical.u b.input.n l __src)
      (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Physical b.input.n l)
    (@DecrAlmostLinearSSSP.Decremental.applyPhysical b.input.n l
      (have __src :=
        @DecrAlmostLinearSSSP.Decremental.indexedPhysical b (DecrAlmostLinearSSSP.Decremental.refresh b s e) l E;
      @DecrAlmostLinearSSSP.Decremental.Physical.mk b.input.n l
        (@DecrAlmostLinearSSSP.Decremental.Physical.graph b.input.n l __src)
        (@DecrAlmostLinearSSSP.Decremental.Physical.active b.input.n l __src)
        (@DecrAlmostLinearSSSP.Decremental.Physical.u b.input.n l __src)
        (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s))
      (@DecrAlmostLinearSSSP.Decremental.CutOp.paired b.input.n l (DecrAlmostLinearSSSP.Decremental.head b e)
        (DecrAlmostLinearSSSP.Decremental.tail b e)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
            (DecrAlmostLinearSSSP.Decremental.labels b s) e)
          (@DecrAlmostLinearSSSP.Decremental.State.cache b s e))))
    (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b (DecrAlmostLinearSSSP.Decremental.refresh b s e) l E)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (c t : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l) (K ξ : Real)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (v : Fin b.input.n),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E s c →
    @DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n l K ξ c
        (@DecrAlmostLinearSSSP.Decremental.CutOp.queryY b.input.n l v) g t →
      And (@Eq.{1} (DecrAlmostLinearSSSP.Decremental.CutState b.input.n l) t c)
        (@Eq.{1} Real (g.realReg (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
          (@DecrAlmostLinearSSSP.Decremental.State.y b s v)))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (c c1 c2 c3 : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l)
  (K ξ : Real) (g1 g2 g3 : DecrAlmostLinearSSSP.Decremental.Machine),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E s c →
    @DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n l K ξ c
        (@DecrAlmostLinearSSSP.Decremental.CutOp.erase b.input.n l
          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
            (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
              (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
              (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
            E e))
        g1 c1 →
      @DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n l K ξ c1
          (@DecrAlmostLinearSSSP.Decremental.CutOp.insert b.input.n l
            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
              (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
                (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
              E e)
            (DecrAlmostLinearSSSP.Decremental.tail b e) (DecrAlmostLinearSSSP.Decremental.head b e)
            (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
              (DecrAlmostLinearSSSP.Decremental.labels b s) e))
          g2 c2 →
        @DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n l K ξ c2
            (@DecrAlmostLinearSSSP.Decremental.CutOp.paired b.input.n l (DecrAlmostLinearSSSP.Decremental.head b e)
              (DecrAlmostLinearSSSP.Decremental.tail b e)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                  (DecrAlmostLinearSSSP.Decremental.labels b s) e)
                (@DecrAlmostLinearSSSP.Decremental.State.cache b s e)))
            g3 c3 →
          @DecrAlmostLinearSSSP.Decremental.CutModel b l E (DecrAlmostLinearSSSP.Decremental.refresh b s e) c3) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
  (c : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l),
  @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Physical b.input.n l)
      (@DecrAlmostLinearSSSP.Decremental.CutState.physical b.input.n l c)
      (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b (DecrAlmostLinearSSSP.Decremental.initializeState b) l E) →
    @Eq.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.CutState.y b.input.n l c)
        (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
          (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
            (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero))) →
      @Eq.{1} (Fin l → Real) (@DecrAlmostLinearSSSP.Decremental.CutState.baseline b.input.n l c)
          (@OfNat.ofNat.{0} (Fin l → Real) (nat_lit 0)
            (@Zero.toOfNat0.{0} (Fin l → Real) (@Pi.instZero.{0, 0} (Fin l) (fun a => Real) fun i => Real.instZero))) →
        @DecrAlmostLinearSSSP.Decremental.CutModel b l E (DecrAlmostLinearSSSP.Decremental.initializeState b) c) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
        ∀ {l : Nat} (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)),
          @LE.le.{0} Nat instLENat l
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size) →
            ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
              have before := @DecrAlmostLinearSSSP.Decremental.indexedPhysical b s l E;
              have erased :=
                @DecrAlmostLinearSSSP.Decremental.applyPhysical b.input.n l before
                  (@DecrAlmostLinearSSSP.Decremental.CutOp.erase b.input.n l
                    (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                      (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
                      (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                        (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
                        (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
                      E e));
              have inserted :=
                @DecrAlmostLinearSSSP.Decremental.applyPhysical b.input.n l erased
                  (@DecrAlmostLinearSSSP.Decremental.CutOp.insert b.input.n l
                    (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                      (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
                      (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                        (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
                        (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
                      E e)
                    (DecrAlmostLinearSSSP.Decremental.tail b e) (DecrAlmostLinearSSSP.Decremental.head b e)
                    (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                      (DecrAlmostLinearSSSP.Decremental.labels b s) e));
              have paired :=
                @DecrAlmostLinearSSSP.Decremental.applyPhysical b.input.n l inserted
                  (@DecrAlmostLinearSSSP.Decremental.CutOp.paired b.input.n l
                    (DecrAlmostLinearSSSP.Decremental.head b e) (DecrAlmostLinearSSSP.Decremental.tail b e)
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                        (DecrAlmostLinearSSSP.Decremental.labels b s) e)
                      (@DecrAlmostLinearSSSP.Decremental.State.cache b s e)));
              And
                (@DecrAlmostLinearSSSP.Decremental.Physical.Valid b.input.n l erased
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))))
                (And
                  (@DecrAlmostLinearSSSP.Decremental.Physical.Valid b.input.n l inserted
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))))
                  (And
                    (@Eq.{1} (DecrAlmostLinearSSSP.Decremental.Physical b.input.n l) paired
                      (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b
                        (DecrAlmostLinearSSSP.Decremental.refresh b s e) l E))
                    (@DecrAlmostLinearSSSP.Decremental.Physical.Valid b.input.n l paired
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))))))))))) ∧ (((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (c : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l) (K : Real),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E s c →
    @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.CutState.hasCut b.input.n l c) Bool.true →
      @Ne.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
          (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
            (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
              (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero))) →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n l c) →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) K →
            @DecrAlmostLinearSSSP.Decremental.CutOp.Valid b.input.n l c
              (@DecrAlmostLinearSSSP.Decremental.CutOp.toggle b.input.n l
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n l c))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
    @Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b s)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Ne.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
        (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
          (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
            (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (c : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E s c →
    ∀ (active : Finset.{0} (Fin b.input.k)) (stopped : Bool)
      (history : List.{0} (DecrAlmostLinearSSSP.Decremental.Event b)),
      @DecrAlmostLinearSSSP.Decremental.CutModel b l E
        (@DecrAlmostLinearSSSP.Decremental.State.mk b active (@DecrAlmostLinearSSSP.Decremental.State.y b s)
          (@DecrAlmostLinearSSSP.Decremental.State.cache b s) (@DecrAlmostLinearSSSP.Decremental.State.baseline b s)
          (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
          (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b s)
          (@DecrAlmostLinearSSSP.Decremental.State.sample b s) (@DecrAlmostLinearSSSP.Decremental.State.output b s)
          (@DecrAlmostLinearSSSP.Decremental.State.pending b s) stopped
          (@DecrAlmostLinearSSSP.Decremental.State.toggles b s) history)
        c) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (c : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E s c →
    ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
      @DecrAlmostLinearSSSP.Decremental.CutOp.Valid b.input.n l c
        (@DecrAlmostLinearSSSP.Decremental.CutOp.erase b.input.n l
          (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
            (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
            (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
              (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
              (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
            E e))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {l : Nat}
  (E : Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (c c1 : DecrAlmostLinearSSSP.Decremental.CutState b.input.n l) (K ξ : Real)
  (g : DecrAlmostLinearSSSP.Decremental.Machine),
  @DecrAlmostLinearSSSP.Decremental.CutModel b l E s c →
    ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
      @DecrAlmostLinearSSSP.Decremental.CutTransition b.input.n l K ξ c
          (@DecrAlmostLinearSSSP.Decremental.CutOp.erase b.input.n l
            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
              (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
                (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
              E e))
          g c1 →
        @DecrAlmostLinearSSSP.Decremental.CutOp.Valid b.input.n l c1
          (@DecrAlmostLinearSSSP.Decremental.CutOp.insert b.input.n l
            (@DFunLike.coe.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
              (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin l)
              (@EquivLike.toFunLike.{1, 1, 1} (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l))
                (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)
                (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin l)))
              E e)
            (DecrAlmostLinearSSSP.Decremental.tail b e) (DecrAlmostLinearSSSP.Decremental.head b e)
            (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
              (DecrAlmostLinearSSSP.Decremental.labels b s) e))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K s →
        ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b), DecrAlmostLinearSSSP.Decremental.RefreshValidity b s e)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  @DecrAlmostLinearSSSP.Decremental.Physical.Valid b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
      (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b s (DecrAlmostLinearSSSP.Decremental.logicalCount b)
        (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))) →
    @DecrAlmostLinearSSSP.Decremental.Physical.Valid b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
        (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b (DecrAlmostLinearSSSP.Decremental.refresh b s e)
          (DecrAlmostLinearSSSP.Decremental.logicalCount b) (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
          (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))) →
      (∀ (d : DecrAlmostLinearSSSP.Decremental.Edge b),
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (@DecrAlmostLinearSSSP.Decremental.State.cache b s d)) →
        DecrAlmostLinearSSSP.Decremental.RefreshValidity b s e) ∧ ((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 ξ h Γ init : Real}
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
      impl K0 ξ h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
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
                  impl K0 ξ h Γ init s ctx)) →
            ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
              DecrAlmostLinearSSSP.Decremental.RefreshValidity b state e →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
                      (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.tail b e)) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))))
                        (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.head b e)) →
                      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))))
                          (DecrAlmostLinearSSSP.Decremental.capacity b
                            (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                            (DecrAlmostLinearSSSP.Decremental.labels b state) e) →
                        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614))))
                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                              (DecrAlmostLinearSSSP.Decremental.capacity b
                                (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                                (DecrAlmostLinearSSSP.Decremental.labels b state) e)
                              (@DecrAlmostLinearSSSP.Decremental.State.cache b state e)) →
                          ∃ cost t next,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.physicalRefreshCode N impl.program) s
                                cost t)
                              (And
                                (@LE.le.{0} Nat instLENat cost
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0 ξ h Γ init t next).work
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0 ξ h Γ init s ctx).work))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24))) N))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 85) (instOfNatNat (nat_lit 85)))))
                                (And (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t)
                                  (And
                                    (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                                      (DecrAlmostLinearSSSP.Decremental.refresh b state e)
                                      (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init t next)))
                                    (And
                                      (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init t next)
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init s ctx))
                                      (And
                                        (@Eq.{1}
                                          (List.{0}
                                            (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              b.input.size)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                b.weightExponent)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                            impl K0 ξ h Γ init t next)
                                          (@HAppend.hAppend.{0, 0, 0}
                                            (List.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                            (List.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                            (List.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                            (@instHAppendOfAppend.{0}
                                              (List.{0}
                                                (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                              (@List.instAppend.{0}
                                                (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0 ξ h Γ init s ctx)
                                            (@List.cons.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                              (@DecrAlmostLinearSSSP.Decremental.CutOp.erase b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                (@DFunLike.coe.{1, 1, 1}
                                                  (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                    (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                  (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                  (fun x => Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                  (@EquivLike.toFunLike.{1, 1, 1}
                                                    (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                    (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                    (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                    (@Equiv.instEquivLike.{1, 1}
                                                      (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                                  (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) e))
                                              (@List.cons.{0}
                                                (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                (@DecrAlmostLinearSSSP.Decremental.CutOp.insert b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                  (@DFunLike.coe.{1, 1, 1}
                                                    (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                    (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                    (fun x => Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                    (@EquivLike.toFunLike.{1, 1, 1}
                                                      (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                      (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                      (@Equiv.instEquivLike.{1, 1}
                                                        (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                                    (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) e)
                                                  (DecrAlmostLinearSSSP.Decremental.tail b e)
                                                  (DecrAlmostLinearSSSP.Decremental.head b e)
                                                  (DecrAlmostLinearSSSP.Decremental.capacity b
                                                    (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                                                    (DecrAlmostLinearSSSP.Decremental.labels b state) e))
                                                (@List.cons.{0}
                                                  (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                  (@DecrAlmostLinearSSSP.Decremental.CutOp.paired b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                    (DecrAlmostLinearSSSP.Decremental.head b e)
                                                    (DecrAlmostLinearSSSP.Decremental.tail b e)
                                                    (@HSub.hSub.{0, 0, 0} Real Real Real
                                                      (@instHSub.{0} Real Real.instSub)
                                                      (DecrAlmostLinearSSSP.Decremental.capacity b
                                                        (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                                                        (DecrAlmostLinearSSSP.Decremental.labels b state) e)
                                                      (@DecrAlmostLinearSSSP.Decremental.State.cache b state e)))
                                                  (@List.nil.{0}
                                                    (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b))))))))
                                        (And
                                          (@LE.le.{0} Nat instLENat
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0 ξ h Γ init s ctx).work
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0 ξ h Γ init t next).work)
                                          (@Eq.{1} Nat
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
                                                impl K0 ξ h Γ init t next))
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
                                                impl K0 ξ h Γ init s ctx)))))))))) ∧ (∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 ξ h Γ init : Real}
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
      impl K0 ξ h Γ init s),
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
                      impl K0 ξ h Γ init s ctx)) →
                ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                      (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
                        (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.tail b e)) →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))))
                          (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.head b e)) →
                        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))))
                            (DecrAlmostLinearSSSP.Decremental.capacity b
                              (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                              (DecrAlmostLinearSSSP.Decremental.labels b state) e) →
                          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614))))
                              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                                (DecrAlmostLinearSSSP.Decremental.capacity b
                                  (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                                  (DecrAlmostLinearSSSP.Decremental.labels b state) e)
                                (@DecrAlmostLinearSSSP.Decremental.State.cache b state e)) →
                            ∃ cost t next,
                              And
                                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                  (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.physicalRefreshCode N impl.program) s
                                  cost t)
                                (And
                                  (@LE.le.{0} Nat instLENat cost
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0 ξ h Γ init t next).work
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0 ξ h Γ init s ctx).work))
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24))) N))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 85) (instOfNatNat (nat_lit 85)))))
                                  (And (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t)
                                    (And
                                      (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                        (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                                        (DecrAlmostLinearSSSP.Decremental.refresh b state e)
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
                                            impl K0 ξ h Γ init t next)))
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
                                            impl K0 ξ h Γ init t next)
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              b.input.size)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                b.weightExponent)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                            impl K0 ξ h Γ init s ctx))
                                        (And
                                          (@Eq.{1}
                                            (List.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0 ξ h Γ init t next)
                                            (@HAppend.hAppend.{0, 0, 0}
                                              (List.{0}
                                                (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                              (List.{0}
                                                (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                              (List.{0}
                                                (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                              (@instHAppendOfAppend.{0}
                                                (List.{0}
                                                  (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                (@List.instAppend.{0}
                                                  (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0 ξ h Γ init s ctx)
                                              (@List.cons.{0}
                                                (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                (@DecrAlmostLinearSSSP.Decremental.CutOp.erase b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                  (@DFunLike.coe.{1, 1, 1}
                                                    (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                    (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                    (fun x => Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                    (@EquivLike.toFunLike.{1, 1, 1}
                                                      (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                      (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                      (@Equiv.instEquivLike.{1, 1}
                                                        (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                                    (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) e))
                                                (@List.cons.{0}
                                                  (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                  (@DecrAlmostLinearSSSP.Decremental.CutOp.insert b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                    (@DFunLike.coe.{1, 1, 1}
                                                      (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                      (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                      (fun x => Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                      (@EquivLike.toFunLike.{1, 1, 1}
                                                        (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                          (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                        (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                        (@Equiv.instEquivLike.{1, 1}
                                                          (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                          (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) e)
                                                    (DecrAlmostLinearSSSP.Decremental.tail b e)
                                                    (DecrAlmostLinearSSSP.Decremental.head b e)
                                                    (DecrAlmostLinearSSSP.Decremental.capacity b
                                                      (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                                                      (DecrAlmostLinearSSSP.Decremental.labels b state) e))
                                                  (@List.cons.{0}
                                                    (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                    (@DecrAlmostLinearSSSP.Decremental.CutOp.paired b.input.n
                                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                      (DecrAlmostLinearSSSP.Decremental.head b e)
                                                      (DecrAlmostLinearSSSP.Decremental.tail b e)
                                                      (@HSub.hSub.{0, 0, 0} Real Real Real
                                                        (@instHSub.{0} Real Real.instSub)
                                                        (DecrAlmostLinearSSSP.Decremental.capacity b
                                                          (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                                                          (DecrAlmostLinearSSSP.Decremental.labels b state) e)
                                                        (@DecrAlmostLinearSSSP.Decremental.State.cache b state e)))
                                                    (@List.nil.{0}
                                                      (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b))))))))
                                          (And
                                            (@LE.le.{0} Nat instLENat
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    b.input.size)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                      b.weightExponent)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                  impl K0 ξ h Γ init s ctx).work
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    b.input.size)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                      b.weightExponent)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                  impl K0 ξ h Γ init t next).work)
                                            (@Eq.{1} Nat
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
                                                  impl K0 ξ h Γ init t next))
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
                                                  impl K0 ξ h Γ init s ctx)))))))))))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Loaded b state e s →
    (∀ (k : Nat),
        @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
            (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))
              (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628)))
                (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648)))
                  (@List.nil.{0} Nat))))
            k →
          @Eq.{1} Nat (t.natReg k) (s.natReg k)) →
      (∀ (k : Nat),
          @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
              (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600)))
                (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602)))
                  (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604)))
                    (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606)))
                      (@List.nil.{0} Nat)))))
              k →
            @Eq.{1} Real (t.realReg k) (s.realReg k)) →
        DecrAlmostLinearSSSP.Decremental.CoreGeometry.Loaded b state e t) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGeometry.loadCode k)) ∧ ((∀ (root : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568)))) root →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses root
        (DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s)) ∧ ((∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.labelsCode N p) k) ∧ (∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
            (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.labelsCode N p) k)))) ∧ (((∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 52) (instOfNatNat (nat_lit 52))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 54) (instOfNatNat (nat_lit 54))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 636) (instOfNatNat (nat_lit 636))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 638) (instOfNatNat (nat_lit 638))) →
                  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.physicalRefreshCode N p) k) ∧ (∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
        (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.physicalRefreshCode N p) k)) ∧ ((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {e : DecrAlmostLinearSSSP.Decremental.Edge b} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost N : Nat}
  {p : DecrAlmostLinearSSSP.Decremental.Program},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.labelsCode N p) s
      cost t →
    DecrAlmostLinearSSSP.Decremental.CoreGeometry.Loaded b state e s →
      DecrAlmostLinearSSSP.Decremental.CoreGeometry.Loaded b state e t) ∧ ((∀ {base : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost N : Nat}
  {p : DecrAlmostLinearSSSP.Decremental.Program},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.labelsCode N p) s
      cost t →
    DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses base s →
      DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses base t) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
    (DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s))))))))) := by sorry
