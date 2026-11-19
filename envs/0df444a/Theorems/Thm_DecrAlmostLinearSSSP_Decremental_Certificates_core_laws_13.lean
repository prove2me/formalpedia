-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_13
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T17:33:47.048148+00:00
-- url     : https://prove2.me/theorems/5a5a021e-8f36-4ea0-b70e-1e8bae831549
-- title:
--   Uniform core program, near-linear work and normalization
-- statement:
--   Let the graph, labels, caches, cut states and scalar RAM machines be the objects of the normalized decremental SSSP implementation interface. Each component below is universally quantified over its own parameters and representation hypotheses.
--
--   The fixed normalized-core program terminates after initialization and every completed deletion prefix, maintains certified stored answers and supports nine-instruction queries. Its actual work is bounded using the global potential decrease, cut-session work and report bounds, operation debt and subpolynomial overhead. Polynomial-domain normalization then establishes the full maintenance guarantee for the original graph and the independent attained-state toggle bound. A fast dynamic-cut implementation remains an explicit prerequisite.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_13 : (((((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 694) (instOfNatNat (nat_lit 694))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.code k) ∧ (∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 690) (instOfNatNat (nat_lit 690))))
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 692) (instOfNatNat (nat_lit 692))) k)) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgeBody k)) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgeBody
            k) ∧ (∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 692) (instOfNatNat (nat_lit 692))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.code k))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 694) (instOfNatNat (nat_lit 694))) →
            DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.code k) ∧ (@Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.code)
  Bool.true)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (d : Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b) d)) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 690) (instOfNatNat (nat_lit 690))))
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
              ∃ t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgeBody s
                    (@OfNat.ofNat.{0} Nat (nat_lit 33) (instOfNatNat (nat_lit 33))) t)
                  (And (DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state t)
                    (And
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b) d)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (And
                        (@Eq.{1} Nat
                          (t.natMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b) d)))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Fin.val b.input.n
                              (DecrAlmostLinearSSSP.Decremental.tail b
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
                                    (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
                                  d)))))
                        (And
                          (@Eq.{1} Nat
                            (t.natMem
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                                    (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b) d)))
                                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@Fin.val b.input.n
                                (DecrAlmostLinearSSSP.Decremental.head b
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
                                      (@Equiv.instEquivLike.{1, 1}
                                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                        (DecrAlmostLinearSSSP.Decremental.Edge b)))
                                    (@Equiv.symm.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
                                    d)))))
                          (And
                            (@Eq.{1} Nat
                              (t.natMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                                      (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b) d)))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (And
                              (@Eq.{1} Real
                                (t.realMem
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                        (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b) d)))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                (@DecrAlmostLinearSSSP.Decremental.State.cache b state
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
                                      (@Equiv.instEquivLike.{1, 1}
                                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                        (DecrAlmostLinearSSSP.Decremental.Edge b)))
                                    (@Equiv.symm.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
                                    d)))
                              (And
                                (∀ (j : Nat),
                                  @Ne.{1} Nat j
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b) d)))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                                    @Ne.{1} Nat j
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                                              (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b) d)))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
                                      @Ne.{1} Nat j
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                                                (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b) d)))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))) →
                                        @Eq.{1} Nat (t.natMem j) (s.natMem j))
                                (∀ (j : Nat),
                                  @Ne.{1} Nat j
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b) d)))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                                    @Eq.{1} Real (t.realMem j) (s.realMem j)))))))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant b B state upto s →
    @LT.lt.{0} Nat instLTNat upto (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
      ∃ t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgeBody s
            (@OfNat.ofNat.{0} Nat (nat_lit 33) (instOfNatNat (nat_lit 33))) t)
          (And
            (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant b B state
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              t)
            (And
              (∀ (j : Nat),
                (∀ (i : Nat),
                    @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                      ∀ (offset : Nat),
                        @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                          @Ne.{1} Nat j
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) i))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) offset))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                  @Eq.{1} Nat (t.natMem j) (s.natMem j))
              (∀ (j : Nat),
                (∀ (i : Nat),
                    @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                      @Ne.{1} Nat j
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                  @Eq.{1} Real (t.realMem j) (s.realMem j)))))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant b B state upto s →
    ∃ t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgeLoop s
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 35) (instOfNatNat (nat_lit 35)))
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                (DecrAlmostLinearSSSP.Decremental.logicalCount b) upto))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          t)
        (And
          (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant b B state
            (DecrAlmostLinearSSSP.Decremental.logicalCount b) t)
          (And
            (∀ (j : Nat),
              (∀ (i : Nat),
                  @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                    ∀ (offset : Nat),
                      @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                        @Ne.{1} Nat j
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) i))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) offset))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                @Eq.{1} Nat (t.natMem j) (s.natMem j))
            (∀ (j : Nat),
              (∀ (i : Nat),
                  @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                    @Ne.{1} Nat j
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                @Eq.{1} Real (t.realMem j) (s.realMem j))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgeStart s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgesStarted s))) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 690) (instOfNatNat (nat_lit 690))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgeStart k) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state s →
    @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image b.input.n
        (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
        (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state) s →
      DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
        DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B s →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
            (∀ (j : Nat),
                And
                  (@Eq.{1} Nat
                    (s.natMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Eq.{1} Real
                    (s.realMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
              DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant b B state
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgesStarted s)))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state s →
    @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image b.input.n
        (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
        (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state) s →
      DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
        DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B s →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
            (∀ (j : Nat),
                And
                  (@Eq.{1} Nat
                    (s.natMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Eq.{1} Real
                    (s.realMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
              ∃ t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgeStart.seq
                      DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.edgeLoop)
                    s
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 35) (instOfNatNat (nat_lit 35)))
                        (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    t)
                  (And
                    (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant b B state
                      (DecrAlmostLinearSSSP.Decremental.logicalCount b) t)
                    (And
                      (∀ (j : Nat),
                        (∀ (i : Nat),
                            @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                              ∀ (offset : Nat),
                                @LT.lt.{0} Nat instLTNat offset
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                                  @Ne.{1} Nat j
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) i))
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) offset))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                          @Eq.{1} Nat (t.natMem j) (s.natMem j))
                      (∀ (j : Nat),
                        (∀ (i : Nat),
                            @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                              @Ne.{1} Nat j
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                          @Eq.{1} Real (t.realMem j) (s.realMem j))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state upto s →
    @LT.lt.{0} Nat instLTNat upto b.input.n →
      ∃ t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.code s
            (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) t)
          (And
            (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              t)
            (And (@Eq.{1} (Nat → Nat) t.natMem s.natMem)
              (∀ (j : Nat),
                (∀ (v : Nat),
                    @LT.lt.{0} Nat instLTNat v b.input.n →
                      @Ne.{1} Nat j
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (DecrAlmostLinearSSSP.Decremental.logicalCount b) v)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                  @Eq.{1} Real (t.realMem j) (s.realMem j)))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state upto s →
    ∃ t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.gammaLoop s
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) b.input.n upto))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          t)
        (And (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state b.input.n t)
          (And (@Eq.{1} (Nat → Nat) t.natMem s.natMem)
            (∀ (j : Nat),
              (∀ (v : Nat),
                  @LT.lt.{0} Nat instLTNat v b.input.n →
                    @Ne.{1} Nat j
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.logicalCount b) v)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                @Eq.{1} Real (t.realMem j) (s.realMem j))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant b B state
      (DecrAlmostLinearSSSP.Decremental.logicalCount b) s →
    DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      { realReg := s.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))),
        realMem := s.realMem, natMem := s.natMem }) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.EdgeInvariant b B state
      (DecrAlmostLinearSSSP.Decremental.logicalCount b) s →
    ∃ t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
          ((DecrAlmostLinearSSSP.Decremental.Structured.natural
                (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))).seq
            DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.gammaLoop)
          s
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))) b.input.n)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          t)
        (And (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state b.input.n t)
          (And (@Eq.{1} (Nat → Nat) t.natMem s.natMem)
            (∀ (j : Nat),
              (∀ (v : Nat),
                  @LT.lt.{0} Nat instLTNat v b.input.n →
                    @Ne.{1} Nat j
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.logicalCount b) v)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                @Eq.{1} Real (t.realMem j) (s.realMem j)))))))))) ∧ (((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state b.input.n s →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (m : Nat) (ξ cap : Real) (j : Nat),
      @Eq.{1} Nat
        (s.natMem
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          ((@DecrAlmostLinearSSSP.Decremental.cutInitial b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b) p
                (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b state
                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
                m ξ cap).natMem
            j))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state b.input.n s →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (m : Nat) (ξ cap : Real) (j : Nat),
      @Eq.{1} Real
        (s.realMem
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
        ((@DecrAlmostLinearSSSP.Decremental.cutInitial b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b) p
              (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b state
                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
              m ξ cap).realMem
          j))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state s →
    @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image b.input.n
        (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
        (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state) s →
      DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
        DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B s →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
            (∀ (j : Nat),
                And
                  (@Eq.{1} Nat
                    (s.natMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Eq.{1} Real
                    (s.realMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
              ∃ cost t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.code
                    s cost t)
                  (And
                    (@LE.le.{0} Nat instLENat cost
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 85) (instOfNatNat (nat_lit 85))) b.input.size))
                    (And (DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state b.input.n t)
                      (And
                        (∀ (j : Nat),
                          (∀ (i : Nat),
                              @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                                ∀ (offset : Nat),
                                  @LT.lt.{0} Nat instLTNat offset
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                                    @Ne.{1} Nat j
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) i))
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) offset))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                            @Eq.{1} Nat (t.natMem j) (s.natMem j))
                        (∀ (j : Nat),
                          (∀ (i : Nat),
                              @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                                @Ne.{1} Nat j
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                            (∀ (v : Nat),
                                @LT.lt.{0} Nat instLTNat v b.input.n →
                                  @Ne.{1} Nat j
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b) v)))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                              @Eq.{1} Real (t.realMem j) (s.realMem j)))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
    (DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s)))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).natMem
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66))))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 536) (instOfNatNat (nat_lit 536))))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 540) (instOfNatNat (nat_lit 540))))))
            (And
              (@Eq.{1} Real
                ((DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).realMem
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))
                (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))))
              (@Eq.{1} Real
                ((DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).realMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 508) (instOfNatNat (nat_lit 508))))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      @Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).realMem
        (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat
          (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 508) (instOfNatNat (nat_lit 508))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      ∀ (j : Nat),
        @Ne.{1} Nat j (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))) →
          @Ne.{1} Nat j
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
            @Ne.{1} Nat j
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
              And
                (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).natMem j) (s.natMem j))
                (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s).realMem j)
                  (s.realMem j))) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 670) (instOfNatNat (nat_lit 670))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 672) (instOfNatNat (nat_lit 672))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 674) (instOfNatNat (nat_lit 674))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldCode k) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldCode k))))) ∧ ((((∀ {n l : Nat} (p : DecrAlmostLinearSSSP.Decremental.Program) (graph : DecrAlmostLinearSSSP.Decremental.Physical n l)
  (m N : Nat) (ξ cap : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) n →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 536) (instOfNatNat (nat_lit 536)))) l →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 540) (instOfNatNat (nat_lit 540)))) m →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))) ξ →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 508) (instOfNatNat (nat_lit 508)))) cap →
                (∀ (j : Nat),
                    @LT.lt.{0} Nat instLTNat j N →
                      And
                        (@Eq.{1} Nat
                          (s.natMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@Eq.{1} Real
                          (s.realMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                  DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N
                    (@DecrAlmostLinearSSSP.Decremental.cutInitial n l p graph m ξ cap)
                    (DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.fieldResult s)) ∧ (∀ (N k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124))) k) →
    Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))))
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 674) (instOfNatNat (nat_lit 674))) k) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.code N) k)) ∧ ((∀ (N k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.code N) k) ∧ (∀ {n l : Nat} (p : DecrAlmostLinearSSSP.Decremental.Program) (graph : DecrAlmostLinearSSSP.Decremental.Physical n l)
  (m N : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N →
    ∀ (ξ cap : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) n →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 536) (instOfNatNat (nat_lit 536)))) l →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 540) (instOfNatNat (nat_lit 540)))) m →
                  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))) ξ →
                    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 508) (instOfNatNat (nat_lit 508)))) cap →
                      ∃ t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            (DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.code N) s
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) N)
                              (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19))))
                            t)
                          (And
                            (DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N
                              (@DecrAlmostLinearSSSP.Decremental.cutInitial n l p graph m ξ cap) t)
                            (∀ (address : Nat),
                              (∀ (j : Nat),
                                  @LT.lt.{0} Nat instLTNat j N →
                                    @Ne.{1} Nat address
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))) →
                                And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                  (@Eq.{1} Real (t.realMem address) (s.realMem address))))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.GammaInvariant b B state b.input.n s →
    DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
      ∀ (p : DecrAlmostLinearSSSP.Decremental.Program),
        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @Eq.{1} Nat
                (s.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B)
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              (∀ (j : Nat),
                  @LE.le.{0} Nat instLENat N j →
                    And
                      (@Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                ∃ t,
                  And
                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                      (DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.code N) s
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) N)
                        (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19))))
                      t)
                    (And
                      (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                        (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
                        (@DecrAlmostLinearSSSP.Decremental.cutInitial b.input.n
                          (DecrAlmostLinearSSSP.Decremental.logicalCount b) p
                          (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b state
                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                            (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                          (@HPow.hPow.{0, 0, 0} Real Int Real
                            (@instHPow.{0, 0} Real Int
                              (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                            K
                            (@Neg.neg.{0} Int Int.instNegInt
                              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                          (@HPow.hPow.{0, 0, 0} Real Int Real
                            (@instHPow.{0, 0} Real Int
                              (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                            (DecrAlmostLinearSSSP.Decremental.kappa b)
                            (@Neg.neg.{0} Int Int.instNegInt
                              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
                        t)
                      (∀ (address : Nat),
                        @LT.lt.{0} Nat instLTNat address
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B)
                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
                          And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                            (@Eq.{1} Real (t.realMem address) (s.realMem address))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (cost : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestCopy.code s cost t →
        (∀ (j : Nat),
            (∀ (i : Nat),
                @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                  ∀ (offset : Nat),
                    @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                      @Ne.{1} Nat j
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) i))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) offset))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
              @Eq.{1} Nat (t.natMem j) (s.natMem j)) →
          (∀ (j : Nat),
              (∀ (i : Nat),
                  @LT.lt.{0} Nat instLTNat i (DecrAlmostLinearSSSP.Decremental.logicalCount b) →
                    @Ne.{1} Nat j
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                (∀ (v : Nat),
                    @LT.lt.{0} Nat instLTNat v b.input.n →
                      @Ne.{1} Nat j
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (DecrAlmostLinearSSSP.Decremental.logicalCount b) v)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
                  @Eq.{1} Real (t.realMem j) (s.realMem j)) →
            DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (cost : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreInitialSaved.code N) s cost
          t →
        (∀ (address : Nat),
            @LT.lt.{0} Nat instLTNat address
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B)
                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
              And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
          DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (N registers : Nat) (p cut : DecrAlmostLinearSSSP.Decremental.Program),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) registers →
    have B :=
      @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)));
    have K :=
      DecrAlmostLinearSSSP.Decremental.computableCutQuality N
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size);
    ∃ cost t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
          (DecrAlmostLinearSSSP.Decremental.CoreInitialize.bootCutInputCode N registers)
          (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine p b.input))
          cost t)
        (And
          (@LE.le.{0} Nat instLENat cost
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 80000) (instOfNatNat (nat_lit 80000)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 265) (instOfNatNat (nat_lit 265))))
                    b.input.size)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                    (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                      (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 32)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                          (DecrAlmostLinearSSSP.Decremental.logarithm2
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@Nat.cast.{0} Real Real.instNatCast b.input.size)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                        b.input.accuracy))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) registers))
              (@OfNat.ofNat.{0} Nat (nat_lit 105) (instOfNatNat (nat_lit 105)))))
          (And
            (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K (DecrAlmostLinearSSSP.Decremental.initializeState b)
              t)
            (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
              (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) registers
              (@DecrAlmostLinearSSSP.Decremental.cutInitial b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                cut
                (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b
                  (DecrAlmostLinearSSSP.Decremental.initializeState b) (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                (@HPow.hPow.{0, 0, 0} Real Int Real
                  (@instHPow.{0, 0} Real Int
                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                  K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                (@HPow.hPow.{0, 0, 0} Real Int Real
                  (@instHPow.{0, 0} Real Int
                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                  (DecrAlmostLinearSSSP.Decremental.kappa b)
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
              t)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K K0 h Γ init : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (impl : DecrAlmostLinearSSSP.Decremental.CutImplementation),
      DecrAlmostLinearSSSP.Decremental.ImplementsCut impl
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
          K0 h Γ init
          (@HPow.hPow.{0, 0, 0} Real Int Real
            (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))) K
            (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))) →
        ∃ first,
          And
            (DecrAlmostLinearSSSP.Decremental.Ends impl.program
              (@DecrAlmostLinearSSSP.Decremental.cutInitial b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                impl.program
                (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b
                  (DecrAlmostLinearSSSP.Decremental.initializeState b) (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                (@HPow.hPow.{0, 0, 0} Real Int Real
                  (@instHPow.{0, 0} Real Int
                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                  K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                (@HPow.hPow.{0, 0, 0} Real Int Real
                  (@instHPow.{0, 0} Real Int
                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                  (DecrAlmostLinearSSSP.Decremental.kappa b)
                  (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
              first)
            (And
              (@DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                (DecrAlmostLinearSSSP.Decremental.initializeState b)
                (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b) first))
              (And
                (@Eq.{1} Bool
                  (@DecrAlmostLinearSSSP.Decremental.CutState.hasCut b.input.n
                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                    (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b) first))
                  Bool.false)
                (And (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast first.work) init)
                  (DecrAlmostLinearSSSP.Decremental.CutSession impl b.input.n
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
                    h Γ init))))))))))) ∧ ((((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (impl : DecrAlmostLinearSSSP.Decremental.CutImplementation) (K0 h Γ init : Real),
  DecrAlmostLinearSSSP.Decremental.ImplementsCut impl
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
      K0 h Γ init
      (@HPow.hPow.{0, 0, 0} Real Int Real
        (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
        (DecrAlmostLinearSSSP.Decremental.computableCutQuality N
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))) →
    have B :=
      @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)));
    have K :=
      DecrAlmostLinearSSSP.Decremental.computableCutQuality N
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size);
    have registers := DecrAlmostLinearSSSP.Decremental.CoreInitialize.sourceRegisters impl.program;
    ∃ cost t first,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
          (DecrAlmostLinearSSSP.Decremental.CoreInitialize.bootCutCode N impl.program)
          (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine p b.input))
          cost t)
        (And
          (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast cost)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@Nat.cast.{0} Real Real.instNatCast
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 80000) (instOfNatNat (nat_lit 80000)))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 265) (instOfNatNat (nat_lit 265))))
                        b.input.size)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                        (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                          (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@OfNat.ofNat.{0} Real (nat_lit 32)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                              (DecrAlmostLinearSSSP.Decremental.logarithm2
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@Nat.cast.{0} Real Real.instNatCast b.input.size)
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                            b.input.accuracy))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) registers))
                  (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120)))))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@Nat.cast.{0} Real Real.instNatCast
                    (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code))
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                init)))
          (And
            (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K (DecrAlmostLinearSSSP.Decremental.initializeState b)
              t)
            (And
              (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) registers first t)
              (And
                (@DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                  (DecrAlmostLinearSSSP.Decremental.initializeState b)
                  (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b) first))
                (And
                  (@Eq.{1} Bool
                    (@DecrAlmostLinearSSSP.Decremental.CutState.hasCut b.input.n
                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                      (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b) first))
                    Bool.false)
                  (And (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast first.work) init)
                    (And
                      (DecrAlmostLinearSSSP.Decremental.Ends impl.program
                        (@DecrAlmostLinearSSSP.Decremental.cutInitial b.input.n
                          (DecrAlmostLinearSSSP.Decremental.logicalCount b) impl.program
                          (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b
                            (DecrAlmostLinearSSSP.Decremental.initializeState b)
                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                            (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                          (@HPow.hPow.{0, 0, 0} Real Int Real
                            (@instHPow.{0, 0} Real Int
                              (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                            K
                            (@Neg.neg.{0} Int Int.instNegInt
                              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                          (@HPow.hPow.{0, 0, 0} Real Int Real
                            (@instHPow.{0, 0} Real Int
                              (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                            (DecrAlmostLinearSSSP.Decremental.kappa b)
                            (@Neg.neg.{0} Int Int.instNegInt
                              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
                        first)
                      (DecrAlmostLinearSSSP.Decremental.CutSession impl b.input.n
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
                          K
                          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                        h Γ init))))))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (impl : DecrAlmostLinearSSSP.Decremental.CutImplementation) (K0 h Γ init : Real),
  DecrAlmostLinearSSSP.Decremental.ImplementsCut impl
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
      K0 h Γ init
      (@HPow.hPow.{0, 0, 0} Real Int Real
        (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
        (DecrAlmostLinearSSSP.Decremental.computableCutQuality N
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))) →
    have B :=
      @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)));
    have K :=
      DecrAlmostLinearSSSP.Decremental.computableCutQuality N
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size);
    have registers := DecrAlmostLinearSSSP.Decremental.CoreInitialize.sourceRegisters impl.program;
    ∃ cost t ctx,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
          (DecrAlmostLinearSSSP.Decremental.CoreInitialize.bootCutCode N impl.program)
          (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine p b.input))
          cost t)
        (And
          (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast cost)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@Nat.cast.{0} Real Real.instNatCast
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 80000) (instOfNatNat (nat_lit 80000)))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 265) (instOfNatNat (nat_lit 265))))
                        b.input.size)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                        (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                          (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@OfNat.ofNat.{0} Real (nat_lit 32)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                              (DecrAlmostLinearSSSP.Decremental.logarithm2
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@Nat.cast.{0} Real Real.instNatCast b.input.size)
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                            b.input.accuracy))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) registers))
                  (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120)))))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@Nat.cast.{0} Real Real.instNatCast
                    (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code))
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                init)))
          (And
            (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K (DecrAlmostLinearSSSP.Decremental.initializeState b)
              t)
            (And
              (@DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                (DecrAlmostLinearSSSP.Decremental.initializeState b)
                (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B registers
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
                    h Γ init t ctx)))
              (And
                (@Eq.{1} Bool
                  (@DecrAlmostLinearSSSP.Decremental.CutState.hasCut b.input.n
                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                    (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B registers
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
                          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                        h Γ init t ctx)))
                  Bool.false)
                (And
                  (@Eq.{1}
                    (List.{0}
                      (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                        (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B registers
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
                      h Γ init t ctx)
                    (@List.nil.{0}
                      (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                        (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                  (And
                    (@Eq.{1} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B registers
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
                          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                        h Γ init t ctx)
                      (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Machine
                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B registers
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
                          h Γ init t ctx)
                        (@List.nil.{0} DecrAlmostLinearSSSP.Decremental.Machine)))
                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B registers
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
                          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                        h Γ init t ctx)
                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B registers
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
                          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                        h Γ init t ctx)))))))))) ∧ ((@Filter.Tendsto.{0, 0} Nat Nat DecrAlmostLinearSSSP.Decremental.cutLogHeight (@Filter.atTop.{0} Nat Nat.instPreorder)
  (@Filter.atTop.{0} Nat Nat.instPreorder)) ∧ (@Filter.Tendsto.{0, 0} Nat Nat DecrAlmostLinearSSSP.Decremental.cutRoot (@Filter.atTop.{0} Nat Nat.instPreorder)
  (@Filter.atTop.{0} Nat Nat.instPreorder)))) ∧ (((@Filter.Tendsto.{0, 0} Nat Real
  (fun m => @Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.cutRoot m))
  (@Filter.atTop.{0} Nat Nat.instPreorder) (@Filter.atTop.{0} Real Real.instPreorder)) ∧ (∀ (N m : Nat),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (Real.log (DecrAlmostLinearSSSP.Decremental.computableCutQuality N m))
      (Real.log
        (@Nat.cast.{0} Real Real.instNatCast
          (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 8192)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 8192) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8191) (instOfNatNat (nat_lit 8191)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8190) (instOfNatNat (nat_lit 8190)))))))
        (@Nat.cast.{0} Real Real.instNatCast N))
      (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.cutRoot m))))) ∧ ((∀ (N : Nat), DecrAlmostLinearSSSP.Decremental.Subpolynomial (DecrAlmostLinearSSSP.Decremental.computableCutQuality N)) ∧ (∀ (N m : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) N →
    @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      (DecrAlmostLinearSSSP.Decremental.computableCutQuality N m))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (qualityPower : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) qualityPower →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (impl : DecrAlmostLinearSSSP.Decremental.CutImplementation)
      (K0 h Γ init : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K0 →
        @LE.le.{0} Real Real.instLE K0
            (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
          DecrAlmostLinearSSSP.Decremental.ImplementsCut impl
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
              K0 h Γ init
              (@HPow.hPow.{0, 0, 0} Real Int Real
                (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))) →
            have B :=
              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)));
            have K :=
              DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size);
            have registers := DecrAlmostLinearSSSP.Decremental.CoreInitialize.sourceRegisters impl.program;
            ∃ cost t after next,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.initCode qualityPower impl.program)
                  (DecrAlmostLinearSSSP.Decremental.Structured.data
                    (DecrAlmostLinearSSSP.Decremental.initialMachine p b.input))
                  cost t)
                (And (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K after t)
                  (And (DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K after)
                    (And
                      (@DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                        (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) after
                        (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B registers
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
                            h Γ init t next)))
                      (And (@Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b after) Bool.true)
                        (And (DecrAlmostLinearSSSP.Decremental.ReadoutCertificate b after)
                          (And
                            (@Eq.{1} (Finset.{0} (Fin b.input.k))
                              (@DecrAlmostLinearSSSP.Decremental.State.active b after)
                              (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k)))
                            (And
                              (@Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                                (@DecrAlmostLinearSSSP.Decremental.State.pending b after)
                                (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)))
                              (And
                                (DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b after
                                  (@List.length.{0}
                                    (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B registers
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
                                      h Γ init t next))
                                  (DecrAlmostLinearSSSP.Decremental.reportVolume
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B registers
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
                                      h Γ init t next))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                (And
                                  (@Eq.{1} Nat
                                    (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B registers
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
                                            (@ZPow.toPow.{0} Real
                                              (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                          K
                                          (@Neg.neg.{0} Int Int.instNegInt
                                            (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                        h Γ init t next))
                                    (@DecrAlmostLinearSSSP.Decremental.State.toggles b after))
                                  (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast cost)
                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                          (@Nat.cast.{0} Real Real.instNatCast
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 80000)
                                                          (instOfNatNat (nat_lit 80000)))
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          qualityPower
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                            (instOfNatNat (nat_lit 1)))))
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 265) (instOfNatNat (nat_lit 265))))
                                                    b.input.size)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                                                      (@FloorRing.toFloorSemiring.{0} Real Real.instRing
                                                        Real.linearOrder Real.instFloorRing)
                                                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                                        (@instHDiv.{0} Real
                                                          (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                                        (@HMul.hMul.{0, 0, 0} Real Real Real
                                                          (@instHMul.{0} Real Real.instMul)
                                                          (@OfNat.ofNat.{0} Real (nat_lit 32)
                                                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                                                              (@Nat.instAtLeastTwoHAddOfNat
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 31)
                                                                  (instOfNatNat (nat_lit 31)))
                                                                (@Nat.instNeZeroSucc
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 30)
                                                                    (instOfNatNat (nat_lit 30)))))))
                                                          (DecrAlmostLinearSSSP.Decremental.logarithm2
                                                            (@HAdd.hAdd.{0, 0, 0} Real Real Real
                                                              (@instHAdd.{0} Real Real.instAdd)
                                                              (@Nat.cast.{0} Real Real.instNatCast b.input.size)
                                                              (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                                (@One.toOfNat1.{0} Real Real.instOne)))))
                                                        b.input.accuracy))))
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))
                                                  registers))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120)))))
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                              (@Nat.cast.{0} Real Real.instNatCast
                                                (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code))
                                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                                  (@Nat.instAtLeastTwoHAddOfNat
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                                    (@Nat.instNeZeroSucc
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                                            init))
                                        (@Nat.cast.{0} Real Real.instNatCast
                                          (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.credit b registers
                                            impl.program after
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B
                                              registers
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
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B registers
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
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B
                                              registers
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
                                              h Γ init t next))))
                                      (@OfNat.ofNat.{0} Real (nat_lit 7)
                                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 7) Real.instNatCast
                                          (@Nat.instAtLeastTwoHAddOfNat
                                            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                                            (@Nat.instNeZeroSucc
                                              (@OfNat.ofNat.{0} Nat (nat_lit 5)
                                                (instOfNatNat (nat_lit 5))))))))))))))))))) ∧ (∀ (qualityPower : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (v : Nat),
  ∃ d,
    And
      (DecrAlmostLinearSSSP.Decremental.Ends (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreProgram qualityPower p)
        (have __src :=
          DecrAlmostLinearSSSP.Decremental.resume c
            (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreProgram qualityPower p).query;
        { pc := __src.pc, realReg := __src.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) v,
          realMem := __src.realMem, natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
          work := __src.work })
        d)
      (And
        (@LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d.work
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
            (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))))
        (And (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) (c.natMem v))
          (And (@Eq.{1} Real (d.realReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (c.realMem v))
            (And (@Eq.{1} (Nat → Real) d.realMem c.realMem) (@Eq.{1} (Nat → Nat) d.natMem c.natMem))))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (qualityPower : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) qualityPower →
    ∀ (impl : DecrAlmostLinearSSSP.Decremental.CutImplementation) (K0 h Γ init : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K0 →
        @LE.le.{0} Real Real.instLE K0
            (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
          DecrAlmostLinearSSSP.Decremental.ImplementsCut impl
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
              K0 h Γ init
              (@HPow.hPow.{0, 0, 0} Real Int Real
                (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))) →
            have B :=
              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)));
            have K :=
              DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size);
            have registers := DecrAlmostLinearSSSP.Decremental.CoreInitialize.sourceRegisters impl.program;
            ∃ cost c,
              And
                (DecrAlmostLinearSSSP.Decremental.Ends
                  (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreProgram qualityPower impl.program)
                  (DecrAlmostLinearSSSP.Decremental.initialMachine
                    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreProgram qualityPower impl.program) b.input)
                  c)
                (And
                  (@Eq.{1} Nat c.work
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (∃ ready,
                    @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast c.work)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@Nat.cast.{0} Real Real.instNatCast
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 80000) (instOfNatNat (nat_lit 80000)))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) qualityPower
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (@OfNat.ofNat.{0} Nat (nat_lit 265) (instOfNatNat (nat_lit 265))))
                                      b.input.size)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                      (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                                        (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder
                                          Real.instFloorRing)
                                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                            (@OfNat.ofNat.{0} Real (nat_lit 32)
                                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                                                (@Nat.instAtLeastTwoHAddOfNat
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                                                  (@Nat.instNeZeroSucc
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                                            (DecrAlmostLinearSSSP.Decremental.logarithm2
                                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                                (@Nat.cast.{0} Real Real.instNatCast b.input.size)
                                                (@OfNat.ofNat.{0} Real (nat_lit 1)
                                                  (@One.toOfNat1.{0} Real Real.instOne)))))
                                          b.input.accuracy))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))) registers))
                                (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120)))))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@Nat.cast.{0} Real Real.instNatCast
                                  (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code))
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                              init))
                          (@Nat.cast.{0} Real Real.instNatCast
                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Ready.credit b B registers K K0 h Γ init
                              impl (@List.nil.{0} (Fin b.input.k)) (DecrAlmostLinearSSSP.Decremental.Structured.data c)
                              ready)))
                        (@OfNat.ofNat.{0} Real (nat_lit 8)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))))))) ∧ (∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {deleted : List.{0} (Fin b.input.k)}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (r : DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Ready b B N K K0 h Γ init impl deleted s)
  (hB : @LE.le.{0} Nat instLENat b.input.n B) (value : Nat),
  @Eq.{1} Nat
    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Ready.credit b B N K K0 h Γ init impl deleted
      { realReg := s.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) value,
        realMem := s.realMem, natMem := s.natMem }
      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Ready.external b B N K K0 h Γ init impl deleted s r hB value))
    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Ready.credit b B N K K0 h Γ init impl deleted s r)))) ∧ (((∀ {k : Nat} (deleted : List.{0} (Fin k)) (e : Fin k),
  @Eq.{1} (Finset.{0} (Fin k))
    (@DecrAlmostLinearSSSP.Decremental.live k
      (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin k)) (List.{0} (Fin k)) (List.{0} (Fin k))
        (@instHAppendOfAppend.{0} (List.{0} (Fin k)) (@List.instAppend.{0} (Fin k))) deleted
        (@List.cons.{0} (Fin k) e (@List.nil.{0} (Fin k)))))
    (@Finset.erase.{0} (Fin k) (instDecidableEqFin k) (@DecrAlmostLinearSSSP.Decremental.live k deleted) e)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (qualityPower : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) qualityPower →
    ∀ (impl : DecrAlmostLinearSSSP.Decremental.CutImplementation) (K0 h Γ init : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K0 →
        @LE.le.{0} Real Real.instLE K0
            (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
          ∀ (deleted : List.{0} (Fin b.input.k)) (c : DecrAlmostLinearSSSP.Decremental.Machine)
            (ready :
              DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Ready b
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (DecrAlmostLinearSSSP.Decremental.CoreInitialize.sourceRegisters impl.program)
                (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                K0 h Γ init impl deleted (DecrAlmostLinearSSSP.Decremental.Structured.data c))
            (e : Fin b.input.k),
            ∃ cost d,
              And
                (DecrAlmostLinearSSSP.Decremental.Ends
                  (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreProgram qualityPower impl.program)
                  (DecrAlmostLinearSSSP.Decremental.deletionMachine
                    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreProgram qualityPower impl.program) c
                    (@Fin.val b.input.k e))
                  d)
                (And
                  (@Eq.{1} Nat d.work
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work cost)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (∃ next,
                    @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d.work
                          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Ready.credit b
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (DecrAlmostLinearSSSP.Decremental.CoreInitialize.sourceRegisters impl.program)
                          (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                          K0 h Γ init impl deleted (DecrAlmostLinearSSSP.Decremental.Structured.data c) ready))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Ready.credit b
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (DecrAlmostLinearSSSP.Decremental.CoreInitialize.sourceRegisters impl.program)
                          (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                          K0 h Γ init impl
                          (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin b.input.k)) (List.{0} (Fin b.input.k))
                            (List.{0} (Fin b.input.k))
                            (@instHAppendOfAppend.{0} (List.{0} (Fin b.input.k)) (@List.instAppend.{0} (Fin b.input.k)))
                            deleted (@List.cons.{0} (Fin b.input.k) e (@List.nil.{0} (Fin b.input.k))))
                          (DecrAlmostLinearSSSP.Decremental.Structured.data d) next)))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (qualityPower : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) qualityPower →
    ∀ (impl : DecrAlmostLinearSSSP.Decremental.CutImplementation) (K0 h Γ init : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K0 →
        @LE.le.{0} Real Real.instLE K0
            (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
          DecrAlmostLinearSSSP.Decremental.ImplementsCut impl
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
              K0 h Γ init
              (@HPow.hPow.{0, 0, 0} Real Int Real
                (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))) →
            ∀ (ds : List.{0} (Fin b.input.k)),
              ∃ cs last,
                And
                  (DecrAlmostLinearSSSP.Decremental.OnlineRun
                    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreProgram qualityPower impl.program) b.input ds
                    cs)
                  (And
                    (@Eq.{1} Nat (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@List.length.{0} (Fin b.input.k) ds)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (And
                      (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                        (@List.getLast?.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
                        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine last))
                      (And
                        (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Completed b qualityPower impl K0 h Γ init ds
                          last)
                        (∀ (j : Nat) (c : DecrAlmostLinearSSSP.Decremental.Machine),
                          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine) Nat
                                DecrAlmostLinearSSSP.Decremental.Machine
                                (fun as i =>
                                  @LT.lt.{0} Nat instLTNat i
                                    (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine as))
                                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Machine) cs j)
                              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine c) →
                            DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Completed b qualityPower impl K0 h Γ init
                              (@List.take.{0} (Fin b.input.k) j ds) c))))) ∧ ((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {qualityPower : Nat}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {K0 h Γ init : Real} {deleted : List.{0} (Fin b.input.k)}
  {c : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Completed b qualityPower impl K0 h Γ init deleted c →
    And
      (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val b.input.n b.input.source))
        (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))
      (And
        (∀ (v : Fin b.input.n),
          And
            (@LE.le.{0} Nat instLENat (c.natMem (@Fin.val b.input.n v))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Eq.{1} Nat (c.natMem (@Fin.val b.input.n v))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (c.realMem (@Fin.val b.input.n v))))
        (∀ (v : Fin b.input.n),
          And
            (@LE.le.{0} ENNReal ENNReal.instLE (b.input.dist deleted v)
              (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val b.input.n v)))
            (And
              (@LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val b.input.n v))
                (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                  (@instHMul.{0} ENNReal
                    (@Distrib.toMul.{0} ENNReal
                      (@instDistribOfSemiring.{0} ENNReal
                        (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                  (ENNReal.ofReal
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) b.input.accuracy))
                  (b.input.dist deleted v)))
              (Iff
                (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val b.input.n v))
                  (@Top.top.{0} ENNReal ENNReal.instTop))
                (Not
                  (@DecrAlmostLinearSSSP.Decremental.Reachable b.input.n b.input.k b.input.graph
                    (@DecrAlmostLinearSSSP.Decremental.live b.input.k deleted) b.input.source v))))))) ∧ (∀ {b : DecrAlmostLinearSSSP.Decremental.Core} (s : DecrAlmostLinearSSSP.Decremental.State b),
  @LE.le.{0} Nat instLENat (@DecrAlmostLinearSSSP.Decremental.CoreRepair.stoppedBit b s)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) ∧ (((((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
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
      h Γ init s)
  (state : DecrAlmostLinearSSSP.Decremental.State b) (offset : Nat) (T : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Γ →
      @LE.le.{0} Real Real.instLE
          (@Nat.cast.{0} Real Real.instNatCast (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)) T →
        DecrAlmostLinearSSSP.Decremental.CoreRepair.OperationDebt b state
            (@List.length.{0}
              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b))
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
                  K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
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
                  K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
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
                    K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                  h Γ init s ctx))
              (@DecrAlmostLinearSSSP.Decremental.State.toggles b state) →
            @LE.le.{0} Real Real.instLE
              (@Nat.cast.{0} Real Real.instNatCast
                (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.credit b N impl.program state
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
                    h Γ init s ctx)
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
                      K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                    h Γ init s ctx)
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
                      K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                    h Γ init s ctx)))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      init)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@Nat.cast.{0} Real Real.instNatCast
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                          h)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 100)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 100) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 99) (instOfNatNat (nat_lit 99)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 98) (instOfNatNat (nat_lit 98)))))))
                          (@Nat.cast.{0} Real Real.instNatCast
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@OfNat.ofNat.{0} Real (nat_lit 5)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Γ
                                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                                    (@instHPow.{0, 0} Real Nat
                                      (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                    K (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                T))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                              T))
                          (@Nat.cast.{0} Real Real.instNatCast offset))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        h)
                      (@OfNat.ofNat.{0} Real (nat_lit 20)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))))))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Γ
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      T)))
                (@OfNat.ofNat.{0} Real (nat_lit 10)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 10) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))) ∧ (∀ (D C d h Γ K L M : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) D →
    @LE.le.{0} Real Real.instLE
        (@OfNat.ofNat.{0} Real (nat_lit 20)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))))
        C →
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) d →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) Γ →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) K →
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) L →
                @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    M →
                  ∀ (offset : Real),
                    @LE.le.{0} Real Real.instLE
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) offset →
                      @LE.le.{0} Real Real.instLE offset
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 6)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
                            M) →
                        have T :=
                          @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@OfNat.ofNat.{0} Real (nat_lit 1040)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 1040) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1039) (instOfNatNat (nat_lit 1039)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1038) (instOfNatNat (nat_lit 1038)))))))
                                  d)
                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                  (@instHPow.{0, 0} Real Nat
                                    (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                  K (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              (@HPow.hPow.{0, 0, 0} Real Nat Real
                                (@instHPow.{0, 0} Real Nat
                                  (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                L (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            M;
                        @LE.le.{0} Real Real.instLE
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) D h) C)
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (@OfNat.ofNat.{0} Real (nat_lit 5)
                                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                                            (@Nat.instAtLeastTwoHAddOfNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              (@Nat.instNeZeroSucc
                                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Γ
                                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                                              (@instHPow.{0, 0} Real Nat
                                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                              K (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                          T))
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (@OfNat.ofNat.{0} Real (nat_lit 2)
                                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                            (@Nat.instAtLeastTwoHAddOfNat
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                              (@Nat.instNeZeroSucc
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                        T))
                                    offset)
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) D h)
                                  (@OfNat.ofNat.{0} Real (nat_lit 20)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 20) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))))))))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) Γ
                                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                                      (@instHPow.{0, 0} Real Nat
                                        (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                      K (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                  T)))
                            (@OfNat.ofNat.{0} Real (nat_lit 10)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 10) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                          (@OfNat.ofNat.{0} Real (nat_lit 10000)
                                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 10000) Real.instNatCast
                                              (@Nat.instAtLeastTwoHAddOfNat
                                                (@OfNat.ofNat.{0} Nat (nat_lit 9999) (instOfNatNat (nat_lit 9999)))
                                                (@Nat.instNeZeroSucc
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 9998)
                                                    (instOfNatNat (nat_lit 9998)))))))
                                          d)
                                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) D C))
                                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) h))
                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) Γ))
                                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                                    (@instHPow.{0, 0} Real Nat
                                      (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                    K (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                                (@HPow.hPow.{0, 0, 0} Real Nat Real
                                  (@instHPow.{0, 0} Real Nat
                                    (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                  L (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              M)
                            (@OfNat.ofNat.{0} Real (nat_lit 10)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 10) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))))) ∧ ((∀ (m : Nat),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (DecrAlmostLinearSSSP.Decremental.coreLogOverhead m)) ∧ (DecrAlmostLinearSSSP.Decremental.Subpolynomial DecrAlmostLinearSSSP.Decremental.coreLogOverhead))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.A b)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 65)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 65) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))))))
        (DecrAlmostLinearSSSP.Decremental.coreLogOverhead b.input.size))
      b.input.accuracy)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE
    (Real.log
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (DecrAlmostLinearSSSP.Decremental.Q b)))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@Nat.cast.{0} Real Real.instNatCast
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.weightExponent
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
      (DecrAlmostLinearSSSP.Decremental.coreLogOverhead b.input.size)))) ∧ ((∀ (h Γ a : Nat → Real) (N : Nat),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial h →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial Γ →
      DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
        DecrAlmostLinearSSSP.Decremental.Subpolynomial (DecrAlmostLinearSSSP.Decremental.coreRuntimeOverhead h Γ a N)) ∧ ((∀ (h Γ a : Nat → Real) (N m : Nat),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (h
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)) →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (Γ
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)) →
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (a
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)) →
        @LE.le.{0} Real Real.instLE
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (a
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
          (DecrAlmostLinearSSSP.Decremental.coreRuntimeOverhead h Γ a N m)) ∧ (∀ (h Γ a : Nat → Real) (N m : Nat),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (a
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)) →
    @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (h
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (Γ
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (DecrAlmostLinearSSSP.Decremental.computableCutQuality N
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (DecrAlmostLinearSSSP.Decremental.coreLogOverhead m)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (DecrAlmostLinearSSSP.Decremental.coreRuntimeOverhead h Γ a N m)))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
        @LE.le.{0} Real Real.instLE
          (@Nat.cast.{0} Real Real.instNatCast (@DecrAlmostLinearSSSP.Decremental.State.toggles b s))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 1040)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 1040) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat
                          (@OfNat.ofNat.{0} Nat (nat_lit 1039) (instOfNatNat (nat_lit 1039)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1038) (instOfNatNat (nat_lit 1038)))))))
                    (@Nat.cast.{0} Real Real.instNatCast
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.weightExponent
                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (@Nat.cast.{0} Real Real.instNatCast b.input.size))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (DecrAlmostLinearSSSP.Decremental.coreLogOverhead b.input.size)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            b.input.accuracy)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (N : Nat) (h Γ a : Nat → Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (h
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (Γ
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (a
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
        have m := @Nat.cast.{0} Real Real.instNatCast b.input.size;
        have M :=
          @HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            m b.input.accuracy;
        have O := DecrAlmostLinearSSSP.Decremental.coreRuntimeOverhead h Γ a N b.input.size;
        have K :=
          DecrAlmostLinearSSSP.Decremental.computableCutQuality N
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size);
        have L := DecrAlmostLinearSSSP.Decremental.coreLogOverhead b.input.size;
        And (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) M)
          (And (@LE.le.{0} Real Real.instLE m M)
            (And
              (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) L)
              (And
                (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  O)
                (And
                  (@LE.le.{0} Real Real.instLE
                    (a
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                    O)
                  (And
                    (@LE.le.{0} Real Real.instLE
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (h
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)))
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (Γ
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))))
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            K (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) L
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      O)
                    (@LE.le.{0} Real Real.instLE
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) L b.input.accuracy)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) O M))))))))) ∧ ((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {qualityPower : Nat},
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) qualityPower →
    ∀ {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} (K0 C : Real) (h Γ a : Nat → Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (h
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (Γ
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (a
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
              ∀ {ds : List.{0} (Fin b.input.k)} {c : DecrAlmostLinearSSSP.Decremental.Machine},
                @DecrAlmostLinearSSSP.Decremental.Legal b.input.k ds →
                  DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Completed b qualityPower impl K0
                      (h
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                      (Γ
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            (@Nat.cast.{0} Real Real.instNatCast b.input.size)))
                        (a
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)))
                      ds c →
                    @LE.le.{0} Real Real.instLE
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                            (@List.length.{0} (Fin b.input.k) ds))))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreConstant b.weightExponent qualityPower
                              impl.program C)
                            (@Nat.cast.{0} Real Real.instNatCast b.input.size))
                          (DecrAlmostLinearSSSP.Decremental.coreRuntimeOverhead h Γ a qualityPower b.input.size))
                        b.input.accuracy)) ∧ (∀ (C : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
    ∀ (m : Nat),
      @LE.le.{0} Real Real.instLE
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
            (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (Real.log
                (@Nat.cast.{0} Real Real.instNatCast
                  (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 5)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                (@OfNat.ofNat.{0} Real (nat_lit 6)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))))
          (@Max.max.{0} Real Real.instMax (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (Real.log
              (Real.log
                (@Nat.cast.{0} Real Real.instNatCast
                  (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 12)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 12) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))))
            C)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.cutRoot m))
            (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))))))) ∧ (((∀ (C : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
    ∃ N,
      And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) N)
        (∀ (m : Nat),
          @LE.le.{0} Real Real.instLE
            (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                  (@HPow.hPow.{0, 0, 0} Real Real Real (@instHPow.{0, 0} Real Real Real.instPow)
                    (Real.log
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 5)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                      (@OfNat.ofNat.{0} Real (nat_lit 6)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))))
                (@Max.max.{0} Real Real.instMax
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (Real.log
                    (Real.log
                      (@Nat.cast.{0} Real Real.instNatCast
                        (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          m)))))))
            (DecrAlmostLinearSSSP.Decremental.computableCutQuality N m))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (qualityPower : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) qualityPower →
    ∀ (impl : DecrAlmostLinearSSSP.Decremental.CutImplementation) (K0 C : Real) (h Γ a : Nat → Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            (h
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
          @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (Γ
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (a
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
              @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  K0 →
                @LE.le.{0} Real Real.instLE K0
                    (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) →
                  DecrAlmostLinearSSSP.Decremental.ImplementsCut impl
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                      K0
                      (h
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                      (Γ
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            (@Nat.cast.{0} Real Real.instNatCast b.input.size)))
                        (a
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)))
                      (@HPow.hPow.{0, 0, 0} Real Int Real
                        (@instHPow.{0, 0} Real Int
                          (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                        (DecrAlmostLinearSSSP.Decremental.computableCutQuality qualityPower
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
                        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))) →
                    DecrAlmostLinearSSSP.Decremental.Maintains
                      (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreProgram qualityPower impl.program)
                      (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreConstant b.weightExponent qualityPower
                        impl.program C)
                      (DecrAlmostLinearSSSP.Decremental.coreRuntimeOverhead h Γ a qualityPower)
                      (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) Bool.false b.input)) ∧ ((∀ (d N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.coreConstant d N p C)) ∧ ((∀ (d : Nat),
  (∃ impl K h Γ a C,
      And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
        (And (DecrAlmostLinearSSSP.Decremental.Subpolynomial K)
          (And (DecrAlmostLinearSSSP.Decremental.Subpolynomial h)
            (And (DecrAlmostLinearSSSP.Decremental.Subpolynomial Γ)
              (And (DecrAlmostLinearSSSP.Decremental.Subpolynomial a)
                (And
                  (∀ (m : Nat),
                    And
                      (@LE.le.{0} Real Real.instLE
                        (@OfNat.ofNat.{0} Real (nat_lit 32)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                        (K m))
                      (@LE.le.{0} Real Real.instLE (K m)
                        (Real.rpow
                          (@OfNat.ofNat.{0} Real (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                              ((Real.log
                                    (@Nat.cast.{0} Real Real.instNatCast
                                      (@Max.max.{0} Nat Nat.instMax
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))).rpow
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                  (@OfNat.ofNat.{0} Real (nat_lit 5)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 5) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                  (@OfNat.ofNat.{0} Real (nat_lit 6)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))))
                            (@Max.max.{0} Real Real.instMax
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (Real.log
                                (Real.log
                                  (@Nat.cast.{0} Real Real.instNatCast
                                    (@Max.max.{0} Nat Nat.instMax
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))))))))
                  (∀ (m : Nat) (ξ : Real),
                    @LT.lt.{0} Real Real.instLT
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) ξ →
                      DecrAlmostLinearSSSP.Decremental.ImplementsCut impl m
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) d)
                          (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                        (K m) (h m) (Γ m)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                            (@Nat.cast.{0} Real Real.instNatCast m))
                          (a m))
                        ξ))))))) →
    ∃ p C a,
      And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
        (And (DecrAlmostLinearSSSP.Decremental.Subpolynomial a)
          (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
            @Eq.{1} Nat b.weightExponent d →
              DecrAlmostLinearSSSP.Decremental.Maintains p C a
                (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) Bool.false b.input))) ∧ (∀ (d : Nat),
  (∃ p C a,
      And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
        (And (DecrAlmostLinearSSSP.Decremental.Subpolynomial a)
          (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
            @Eq.{1} Nat b.weightExponent
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
              DecrAlmostLinearSSSP.Decremental.Maintains p C a
                (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) Bool.false b.input))) →
    ∃ p C a queryBound,
      And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C)
        (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) queryBound)
          (And (DecrAlmostLinearSSSP.Decremental.Subpolynomial a)
            (And
              (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
                i.Valid →
                  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
                    @LE.le.{0} Nat instLENat i.W
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                          i.size d) →
                      @LT.lt.{0} Real Real.instLT
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@Nat.cast.{0} Real Real.instNatCast i.size))
                          i.accuracy →
                        @LT.lt.{0} Real Real.instLT i.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                          DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false i)
              (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
                @LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 32)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                    K →
                  ∀ (choose : DecrAlmostLinearSSSP.Decremental.State b → DecrAlmostLinearSSSP.Decremental.CutReply b),
                    DecrAlmostLinearSSSP.Decremental.CutQuality b K choose →
                      ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
                        DecrAlmostLinearSSSP.Decremental.Attained b K choose s →
                          @LE.le.{0} Real Real.instLE
                            (@Nat.cast.{0} Real Real.instNatCast (@DecrAlmostLinearSSSP.Decremental.State.toggles b s))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                    (@OfNat.ofNat.{0} Real (nat_lit 16)
                                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                        (@Nat.instAtLeastTwoHAddOfNat
                                          (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
                                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                                      (@instHPow.{0, 0} Real Nat
                                        (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                                      K (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (DecrAlmostLinearSSSP.Decremental.A b))
                                (@Nat.cast.{0} Real Real.instNatCast b.input.size))
                              (Real.log
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                  (DecrAlmostLinearSSSP.Decremental.Q b)))))))))))))))) := by sorry
