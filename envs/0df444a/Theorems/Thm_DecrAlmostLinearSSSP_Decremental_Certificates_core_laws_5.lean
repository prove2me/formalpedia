-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_5
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T17:33:21.346502+00:00
-- url     : https://prove2.me/theorems/3b740cb2-4c55-4b46-85a7-bd7df8cad90b
-- title:
--   Core memory layout and native parameter construction
-- statement:
--   Let the graph, labels, caches, cut states and scalar RAM machines be the objects of the normalized decremental SSSP implementation interface. Each component below is universally quantified over its own parameters and representation hypotheses.
--
--   Logical core and return identifiers have injective encodings and disjoint physical record addresses. Native routines construct the core parameters, gradient cells, return-vertex indexing and control layout using scalar instructions. Register, address and memory contracts identify every unaffected part of the representation.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_5 : (((((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  @LT.lt.{0} Nat instLTNat (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (DecrAlmostLinearSSSP.Decremental.logicalCount b))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (DecrAlmostLinearSSSP.Decremental.CoreMemory.queueToken b e))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGeometry.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
    (DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.addressed s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568)))))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.addressed s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 574) (instOfNatNat (nat_lit 574))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.addressed s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 576) (instOfNatNat (nat_lit 576))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.addressed s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 578) (instOfNatNat (nat_lit 578))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.addressed s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
    And
      (@Eq.{1} Real
        ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).realReg
          (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))))
        (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))))
      (And
        (@Eq.{1} Real
          ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).realReg
            (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))))
          (s.realMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (And
          (@Eq.{1} Real
            ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).realReg
              (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604))))
            (s.realMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          (And
            (@Eq.{1} Real
              ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).realReg
                (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))))
              (s.realMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
                (s.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))))
                  (s.natMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreGeometry.result s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648))))
                  (s.natMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))))))))) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreGeometry.code)) ∧ ((∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 574) (instOfNatNat (nat_lit 574))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))) k) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGeometry.code k) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreGeometry.code k) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRecord.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) (DecrAlmostLinearSSSP.Decremental.CoreRecord.result s)))))) ∧ ((((∀ (base : Nat) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses base s →
    (∀ (k : Nat),
        @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
            (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568)))
              (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 574) (instOfNatNat (nat_lit 574)))
                (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 576) (instOfNatNat (nat_lit 576)))
                  (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 578) (instOfNatNat (nat_lit 578)))
                    (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580)))
                      (@List.nil.{0} Nat))))))
            k →
          @Eq.{1} Nat (t.natReg k) (s.natReg k)) →
      DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses base t) ∧ (∀ (base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses base s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      And
        (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).natMem base)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628)))))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).natMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648)))))
                (And
                  (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).realMem base)
                    (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612)))))
                  (And
                    (@Eq.{1} Real
                      ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).realMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602)))))
                    (And
                      (@Eq.{1} Real
                        ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).realMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                        (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604)))))
                      (And
                        (@Eq.{1} Real
                          ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).realMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                          (s.realMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
                        (@Eq.{1} Real
                          ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).realMem
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
                          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))))))))))))))) ∧ ((∀ (base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses base s →
    ∀ (j : Nat),
      @Ne.{1} Nat j base →
        @Ne.{1} Nat j
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
          @Ne.{1} Nat j
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
            @Ne.{1} Nat j
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
              @Ne.{1} Nat j
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
                And (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).natMem j) (s.natMem j))
                  (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.CoreRecord.result s).realMem j) (s.realMem j))) ∧ (∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRecord.code k))) ∧ (((∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRecord.code k) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
    (DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.result s))) ∧ ((∀ (B e : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) e))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.result s)) ∧ ((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.code) ∧ (∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.code k)))))) ∧ (((((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreEdgeAddress.code k) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.result s))) ∧ ((∀ (base v q : Nat) (A : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554)))) base →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) v →
      @Eq.{1} Nat
          (s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v)))
          q →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 504) (instOfNatNat (nat_lit 504)))) A →
          @Eq.{1} Real
            ((DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.result s).realReg
              (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) A
              (@Nat.cast.{0} Real Real.instNatCast q))) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.code))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 662) (instOfNatNat (nat_lit 662))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.code k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreReturnCoefficient.code k)) ∧ ((∀ (vertex : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreDegree.code vertex) s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.CoreDegree.result vertex s)) ∧ ((∀ (vertex base v : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554)))) base →
    @Eq.{1} Nat (s.natReg vertex) v →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        And
          (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CoreDegree.result vertex s).natMem
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CoreDegree.result vertex s).realMem s.realMem)) ∧ (∀ {n : Nat} (vertex base : Nat) (v : Fin n) (heads : List.{0} (Fin n))
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.CoreDegree.Image n base heads s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554)))) base →
      @Eq.{1} Nat (s.natReg vertex) (@Fin.val n v) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @DecrAlmostLinearSSSP.Decremental.CoreDegree.Image n base (@List.cons.{0} (Fin n) v heads)
            (DecrAlmostLinearSSSP.Decremental.CoreDegree.result vertex s)))))) ∧ ((((∀ (vertex k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 662) (instOfNatNat (nat_lit 662))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.CoreDegree.code vertex) k) ∧ (∀ (vertex k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.CoreDegree.code vertex) k)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (t : Nat) (v : Fin b.input.n),
  @Eq.{1} Nat
    (@List.count.{0} (Fin b.input.n) (@instBEqOfDecidableEq.{0} (Fin b.input.n) (instDecidableEqFin b.input.n)) v
      (DecrAlmostLinearSSSP.Decremental.CoreDegree.heads b t))
    (@List.length.{0} (Fin b.input.k)
      (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency b.input.n b.input.k
        (DecrAlmostLinearSSSP.Decremental.CoreDegree.reverseGraph b) t v))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (v : Fin b.input.n),
  @Eq.{1} Nat
    (@List.count.{0} (Fin b.input.n) (@instBEqOfDecidableEq.{0} (Fin b.input.n) (instDecidableEqFin b.input.n)) v
      (DecrAlmostLinearSSSP.Decremental.CoreDegree.heads b b.input.k))
    (DecrAlmostLinearSSSP.Decremental.indegree b v)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.CoreDegree.Image b.input.n base
      (DecrAlmostLinearSSSP.Decremental.CoreDegree.heads b b.input.k) s →
    ∀ (v : Fin b.input.n),
      @Eq.{1} Nat
        (s.natMem
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val b.input.n v))))
        (DecrAlmostLinearSSSP.Decremental.indegree b v))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreTape.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (DecrAlmostLinearSSSP.Decremental.CoreTape.result s)) ∧ (∀ (pointer a z w : Nat) (Q : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 652) (instOfNatNat (nat_lit 652)))) pointer →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 502) (instOfNatNat (nat_lit 502)))) Q →
        @Eq.{1} Nat (s.natMem pointer) a →
          @Eq.{1} Nat
              (s.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pointer
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              z →
            @Eq.{1} Nat
                (s.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pointer
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                w →
              And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreTape.result s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
                  a)
                (And
                  (@Eq.{1} Nat
                    ((DecrAlmostLinearSSSP.Decremental.CoreTape.result s).natReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))))
                    z)
                  (And
                    (@Eq.{1} Nat
                      ((DecrAlmostLinearSSSP.Decremental.CoreTape.result s).natReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 654) (instOfNatNat (nat_lit 654))))
                      w)
                    (And
                      (@Eq.{1} Nat
                        ((DecrAlmostLinearSSSP.Decremental.CoreTape.result s).natReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 652) (instOfNatNat (nat_lit 652))))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pointer
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                      (@Eq.{1} Real
                        ((DecrAlmostLinearSSSP.Decremental.CoreTape.result s).realReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604))))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@Nat.cast.{0} Real Real.instNatCast w) Q))))))) ∧ ((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreTape.code) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 652) (instOfNatNat (nat_lit 652))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 654) (instOfNatNat (nat_lit 654))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreTape.code k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 604) (instOfNatNat (nat_lit 604))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreTape.code k))))))) ∧ ((((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
    ∃ cost,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.code s
          cost (DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.result s))
        (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (e : Fin b.input.k)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
      (@Fin.val b.input.n (@DecrAlmostLinearSSSP.Decremental.Digraph.tail b.input.n b.input.k b.input.graph e)) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
        (@Fin.val b.input.n b.input.source) →
      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 514) (instOfNatNat (nat_lit 514))))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (DecrAlmostLinearSSSP.Decremental.Q b))) →
        @Eq.{1} Real
          ((DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.result s).realReg
            (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (DecrAlmostLinearSSSP.Decremental.initialLabel b
              (DecrAlmostLinearSSSP.Decremental.tail b
                (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)))
            (DecrAlmostLinearSSSP.Decremental.initialLabel b
              (DecrAlmostLinearSSSP.Decremental.head b
                (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)))))) ∧ ((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.code) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.code k))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreInitialDifference.code k) ∧ (∀ (bound : Nat),
  ∃ h,
    @LT.lt.{0} Nat instLTNat bound
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.flagCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.flagged s)) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.flagCode
      k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.flagCode
      k))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (e : Fin b.input.k)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape b.input s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
            (@Fin.val b.input.n b.input.source) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val b.input.k e)) →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 652) (instOfNatNat (nat_lit 652))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Fin.val b.input.k e))) →
                @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 502) (instOfNatNat (nat_lit 502))))
                      (DecrAlmostLinearSSSP.Decremental.Q b) →
                    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 514) (instOfNatNat (nat_lit 514))))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            (DecrAlmostLinearSSSP.Decremental.Q b))) →
                      ∃ cost t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.code s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@OfNat.ofNat.{0} Nat (nat_lit 25) (instOfNatNat (nat_lit 25))))
                            (And (DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.Loaded b B e t)
                              (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreParameters.hCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.CoreParameters.hData s))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreParameters.qCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.CoreParameters.qData s)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreParameters.argumentCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
    (DecrAlmostLinearSSSP.Decremental.CoreParameters.argumentData s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreParameters.header s
    (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
    (DecrAlmostLinearSSSP.Decremental.CoreParameters.headed s))))) ∧ (((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreParameters.header) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreParameters.header k)) ∧ ((∀ (k : Nat),
  And (@Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 500) (instOfNatNat (nat_lit 500))))
      (And (@Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 502) (instOfNatNat (nat_lit 502))))
        (And (@Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))))
          (And (@Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 522) (instOfNatNat (nat_lit 522))))
            (@Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 524) (instOfNatNat (nat_lit 524))))))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreParameters.header k) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i (DecrAlmostLinearSSSP.Decremental.CoreParameters.headed s)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) b.input.n →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 70) (instOfNatNat (nat_lit 70)))) b.input.W →
      @Eq.{1} Real
        ((DecrAlmostLinearSSSP.Decremental.CoreParameters.hData s).realReg
          (@OfNat.ofNat.{0} Nat (nat_lit 500) (instOfNatNat (nat_lit 500))))
        (DecrAlmostLinearSSSP.Decremental.H b))))))) ∧ (((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) b.input.n →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 500) (instOfNatNat (nat_lit 500))))
        (DecrAlmostLinearSSSP.Decremental.H b) →
      @Eq.{1} Real
        ((DecrAlmostLinearSSSP.Decremental.CoreParameters.qData s).realReg
          (@OfNat.ofNat.{0} Nat (nat_lit 502) (instOfNatNat (nat_lit 502))))
        (DecrAlmostLinearSSSP.Decremental.Q b)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) b.input.size →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) b.input.accuracy →
        @Eq.{1} Real
          ((DecrAlmostLinearSSSP.Decremental.CoreParameters.argumentData s).realReg
            (@OfNat.ofNat.{0} Nat (nat_lit 522) (instOfNatNat (nat_lit 522))))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 32)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
              (DecrAlmostLinearSSSP.Decremental.logarithm2
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@Nat.cast.{0} Real Real.instNatCast b.input.size)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
            b.input.accuracy))) ∧ ((DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreParameters.argumentCode
  (@OfNat.ofNat.{0} Nat (nat_lit 500) (instOfNatNat (nat_lit 500)))) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreParameters.argumentCode
  (@OfNat.ofNat.{0} Nat (nat_lit 502) (instOfNatNat (nat_lit 502)))))) ∧ (((DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreParameters.qCode
  (@OfNat.ofNat.{0} Nat (nat_lit 500) (instOfNatNat (nat_lit 500)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    @Eq.{1} Real
      ((DecrAlmostLinearSSSP.Decremental.CoreParameters.headed s).realReg
        (@OfNat.ofNat.{0} Nat (nat_lit 500) (instOfNatNat (nat_lit 500))))
      (DecrAlmostLinearSSSP.Decremental.H b))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    @Eq.{1} Real
      ((DecrAlmostLinearSSSP.Decremental.CoreParameters.headed s).realReg
        (@OfNat.ofNat.{0} Nat (nat_lit 502) (instOfNatNat (nat_lit 502))))
      (DecrAlmostLinearSSSP.Decremental.Q b)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    @Eq.{1} Real
      ((DecrAlmostLinearSSSP.Decremental.CoreParameters.headed s).realReg
        (@OfNat.ofNat.{0} Nat (nat_lit 522) (instOfNatNat (nat_lit 522))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 32)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
          (DecrAlmostLinearSSSP.Decremental.logarithm2
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@Nat.cast.{0} Real Real.instNatCast b.input.size)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
        b.input.accuracy)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreParameters.finish s
    (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
    (DecrAlmostLinearSSSP.Decremental.CoreParameters.finished s)))))) ∧ ((((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreParameters.finish) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 500) (instOfNatNat (nat_lit 500))))
        (DecrAlmostLinearSSSP.Decremental.H b) →
      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 502) (instOfNatNat (nat_lit 502))))
          (DecrAlmostLinearSSSP.Decremental.Q b) →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 526) (instOfNatNat (nat_lit 526))))
            (DecrAlmostLinearSSSP.Decremental.A b) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 442) (instOfNatNat (nat_lit 442)))) K →
            DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K
              (DecrAlmostLinearSSSP.Decremental.CoreParameters.finished s))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreControl.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))
    (DecrAlmostLinearSSSP.Decremental.CoreControl.result s)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (B : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
      DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
        And
          (DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B
            (DecrAlmostLinearSSSP.Decremental.CoreControl.result s))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.CoreControl.result s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 546) (instOfNatNat (nat_lit 546))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.CoreControl.result s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreControl.result s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Eq.{1} Real
                  ((DecrAlmostLinearSSSP.Decremental.CoreControl.result s).realReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@Neg.neg.{0} Real Real.instNeg
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 4)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      K))))))) ∧ (∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))) k) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))) →
      Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 542) (instOfNatNat (nat_lit 542))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))) k) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreControl.code k)))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 656) (instOfNatNat (nat_lit 656))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 658) (instOfNatNat (nat_lit 658))) →
        DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreControl.code k) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreControl.code)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input
      (DecrAlmostLinearSSSP.Decremental.CoreControl.result s)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
    DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K (DecrAlmostLinearSSSP.Decremental.CoreControl.result s)) ∧ (∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreControl.code
    (DecrAlmostLinearSSSP.Decremental.shadowReg j))))))))) := by sorry
