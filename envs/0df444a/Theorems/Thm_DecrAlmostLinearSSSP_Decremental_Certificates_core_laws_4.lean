-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_4
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T17:33:20.378027+00:00
-- url     : https://prove2.me/theorems/6f1a5c62-5d37-4f94-a6da-b77e2d6cb72f
-- title:
--   Certified readout and dynamic-cut parameter bounds
-- statement:
--   Let the graph, labels, caches, cut states and scalar RAM machines be the objects of the normalized decremental SSSP implementation interface. Each component below is universally quantified over its own parameters and representation hypotheses.
--
--   The core-distance certificates imply the original all-target readout guarantee, including exact infinity for disconnected targets. Actual stopping states provide the analytic certificate used by that readout. Computable quality bounds dominate the dynamic-cut quality exponent, and the required polynomial ranges follow from the fixed weight exponent and the exact core parameters.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_4 : (((((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (p : Fin b.input.n → Real),
  @Eq.{1} Real (p b.input.source) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
    ∀ (B : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) B →
        ∀ (t : Fin b.input.n),
          @LT.lt.{0} Real Real.instLT
              (@DecrAlmostLinearSSSP.Decremental.cappedDistance b.input.n b.input.k b.input.graph
                (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
                (DecrAlmostLinearSSSP.Decremental.coreLength b active p) B b.input.source t)
              B →
            @LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.coreDistance b active t)
              (ENNReal.ofReal
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (p t)
                  (@DecrAlmostLinearSSSP.Decremental.cappedDistance b.input.n b.input.k b.input.graph
                    (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
                    (DecrAlmostLinearSSSP.Decremental.coreLength b active p) B b.input.source t)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (DecrAlmostLinearSSSP.Decremental.Q b))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (DecrAlmostLinearSSSP.Decremental.H b)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (es : List.{0} (Fin b.input.k)),
  (∀ (e : Fin b.input.k),
      @Membership.mem.{0, 0} (Fin b.input.k) (List.{0} (Fin b.input.k)) (@List.instMembership.{0} (Fin b.input.k)) es
          e →
        @Membership.mem.{0, 0} (Fin b.input.k) (Finset.{0} (Fin b.input.k))
          (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin b.input.k)) (Fin b.input.k)
            (@Finset.instSetLike.{0} (Fin b.input.k)))
          active e) →
    @Eq.{1} Real
      (@List.sum.{0} Real Real.instAdd Real.instZero
        (@List.map.{0, 0} (Fin b.input.k) Real
          (fun e =>
            DecrAlmostLinearSSSP.Decremental.cost b active
              (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e))
          es))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@List.sum.{0} Real Real.instAdd Real.instZero
          (@List.map.{0, 0} (Fin b.input.k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (b.input.weight e)) es))
        (DecrAlmostLinearSSSP.Decremental.Q b))))) ∧ (((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    ∀ (e : Fin k),
      @Membership.mem.{0, 0} (Fin k) (List.{0} (Fin k)) (@List.instMembership.{0} (Fin k)) es e →
        @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
          (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active e) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active all : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g all u v es →
    (∀ (e : Fin k),
        @Membership.mem.{0, 0} (Fin k) (List.{0} (Fin k)) (@List.instMembership.{0} (Fin k)) es e →
          @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
            (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active e) →
      @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (es : List.{0} (Fin b.input.k))
  (e : Fin b.input.k),
  @Membership.mem.{0, 0} (Fin b.input.k) (List.{0} (Fin b.input.k)) (@List.instMembership.{0} (Fin b.input.k)) es e →
    e ∉ active →
      @LE.le.{0} Real Real.instLE
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (DecrAlmostLinearSSSP.Decremental.H b) (DecrAlmostLinearSSSP.Decremental.Q b))
        (@List.sum.{0} Real Real.instAdd Real.instZero
          (@List.map.{0, 0} (Fin b.input.k) Real
            (fun f =>
              DecrAlmostLinearSSSP.Decremental.cost b active
                (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) f))
            es))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (v : Fin b.input.n),
  ∃ es,
    And
      (@DecrAlmostLinearSSSP.Decremental.Walk b.input.n b.input.k b.input.graph
        (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k)) b.input.source v es)
      (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.coreDistance b active v)
        (ENNReal.ofReal
          (@List.sum.{0} Real Real.instAdd Real.instZero
            (@List.map.{0, 0} (Fin b.input.k) Real
              (fun e =>
                DecrAlmostLinearSSSP.Decremental.cost b active
                  (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e))
              es))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (v : Fin b.input.n),
  Not (@DecrAlmostLinearSSSP.Decremental.Reachable b.input.n b.input.k b.input.graph active b.input.source v) →
    @LE.le.{0} ENNReal ENNReal.instLE
      (ENNReal.ofReal
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (DecrAlmostLinearSSSP.Decremental.H b) (DecrAlmostLinearSSSP.Decremental.Q b)))
      (DecrAlmostLinearSSSP.Decremental.coreDistance b active v)))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (v : Fin b.input.n),
  @DecrAlmostLinearSSSP.Decremental.Reachable b.input.n b.input.k b.input.graph active b.input.source v →
    ∃ d,
      And (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) d)
        (And
          (@LE.le.{0} Real Real.instLE d
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Nat.cast.{0} Real Real.instNatCast b.input.n) (@Nat.cast.{0} Real Real.instNatCast b.input.W)))
          (And
            (@Eq.{1} ENNReal
              (@DecrAlmostLinearSSSP.Decremental.distance b.input.n b.input.k b.input.graph active
                (fun e =>
                  @Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (b.input.weight e))
                b.input.source v)
              (ENNReal.ofReal d))
            (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.coreDistance b active v)
              (ENNReal.ofReal
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) d
                  (DecrAlmostLinearSSSP.Decremental.Q b))))))) ∧ (∀ {eps p z r : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eps →
    @LE.le.{0} Real Real.instLE eps (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) p →
        @LE.le.{0} Real Real.instLE p z →
          @LE.le.{0} Real Real.instLE z
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) eps
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                p) →
            @LE.le.{0} Real Real.instLE
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) eps
                      (@OfNat.ofNat.{0} Real (nat_lit 8)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
                  p)
                r →
              @LE.le.{0} Real Real.instLE r
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) eps
                        (@OfNat.ofNat.{0} Real (nat_lit 8)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
                    p) →
                And
                  (@LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r)
                  (And
                    (@LE.le.{0} Real Real.instLE z
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) eps
                            (@OfNat.ofNat.{0} Real (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
                        r))
                    (And
                      (@LE.le.{0} Real Real.instLE
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) eps
                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
                          r)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) eps)
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
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))))
                              (@OfNat.ofNat.{0} Real (nat_lit 10)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 10) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))))
                            z)
                          r)
                        (@LE.le.{0} Real Real.instLE r
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                              (@OfNat.ofNat.{0} Real (nat_lit 9)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 9) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))
                              (@OfNat.ofNat.{0} Real (nat_lit 8)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))))
                            z))))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
            (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
          Or
              (@Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b s)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (∃ r,
                And
                  (@DecrAlmostLinearSSSP.Decremental.RatioGuarantee b.input.n
                    (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                      (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                        (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
                    (DecrAlmostLinearSSSP.Decremental.cachedPhysical b s) K
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
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                        K))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@DecrAlmostLinearSSSP.Decremental.CutReply.G b r)
                      (@DecrAlmostLinearSSSP.Decremental.CutReply.U b r)))) →
            DecrAlmostLinearSSSP.Decremental.ReadoutCertificate b s) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ {s t : DecrAlmostLinearSSSP.Decremental.State b},
      DecrAlmostLinearSSSP.Decremental.RuntimeRepairStep b K s t →
        DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
          DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K t))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ {s t : DecrAlmostLinearSSSP.Decremental.State b},
      DecrAlmostLinearSSSP.Decremental.RuntimeRepairStep b K s t →
        DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
          @Prod.Lex.{0, 0} Nat Nat Nat.lt Nat.lt (DecrAlmostLinearSSSP.Decremental.runtimeRepairRank b K t)
            (DecrAlmostLinearSSSP.Decremental.runtimeRepairRank b K s)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    @WellFounded.{1} (DecrAlmostLinearSSSP.Decremental.State b) fun t s =>
      And (DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s)
        (DecrAlmostLinearSSSP.Decremental.RuntimeRepairStep b K s t))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ {s t : DecrAlmostLinearSSSP.Decremental.State b},
      DecrAlmostLinearSSSP.Decremental.RuntimeRepairStep b K s t →
        DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
          @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b t) Bool.true →
            DecrAlmostLinearSSSP.Decremental.ReadoutCertificate b t) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) {s t : DecrAlmostLinearSSSP.Decremental.State b},
  DecrAlmostLinearSSSP.Decremental.RuntimeRepairStep b K s t →
    @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b t) Bool.true →
      @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b t)
        (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))) ∧ (∀ {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {m exponent : Nat} {K h Γ init ξ : Real},
  DecrAlmostLinearSSSP.Decremental.ImplementsCut impl m exponent K h Γ init ξ →
    ∀ {n k : Nat} (graph : DecrAlmostLinearSSSP.Decremental.Physical n k) (capacityBound : Real),
      @DecrAlmostLinearSSSP.Decremental.Physical.Valid n k graph m exponent →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
            capacityBound →
          @LE.le.{0} Real Real.instLE capacityBound
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@Max.max.{0} Real Real.instMax
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (@Nat.cast.{0} Real Real.instNatCast m))
                exponent) →
            (∀ (e : Fin k),
                @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
                    (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k)))
                    (@DecrAlmostLinearSSSP.Decremental.Physical.active n k graph) e →
                  @LE.le.{0} Real Real.instLE (@DecrAlmostLinearSSSP.Decremental.Physical.u n k graph e)
                    capacityBound) →
              ∃ first,
                And
                  (DecrAlmostLinearSSSP.Decremental.Ends impl.program
                    (@DecrAlmostLinearSSSP.Decremental.cutInitial n k impl.program graph m ξ capacityBound) first)
                  (And
                    (@Eq.{1} (DecrAlmostLinearSSSP.Decremental.Physical n k)
                      (@DecrAlmostLinearSSSP.Decremental.CutState.physical n k (impl.view n k first)) graph)
                    (And
                      (@Eq.{1} (Fin n → Real) (@DecrAlmostLinearSSSP.Decremental.CutState.y n k (impl.view n k first))
                        (@OfNat.ofNat.{0} (Fin n → Real) (nat_lit 0)
                          (@Zero.toOfNat0.{0} (Fin n → Real)
                            (@Pi.instZero.{0, 0} (Fin n) (fun a => Real) fun i => Real.instZero))))
                      (And
                        (@Eq.{1} (Fin k → Real)
                          (@DecrAlmostLinearSSSP.Decremental.CutState.baseline n k (impl.view n k first))
                          (@OfNat.ofNat.{0} (Fin k → Real) (nat_lit 0)
                            (@Zero.toOfNat0.{0} (Fin k → Real)
                              (@Pi.instZero.{0, 0} (Fin k) (fun a => Real) fun i => Real.instZero))))
                        (And
                          (@Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.CutState.hasCut n k (impl.view n k first))
                            Bool.false)
                          (And (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast first.work) init)
                            (DecrAlmostLinearSSSP.Decremental.CutSession impl n k m exponent first K ξ h Γ init)))))))))))) ∧ (((((∀ (cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine) (current final : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
      (@List.getLast?.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine current) →
    @Eq.{1} Nat
      (DecrAlmostLinearSSSP.Decremental.reportVolume
        (@HAppend.hAppend.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
          (List.{0} DecrAlmostLinearSSSP.Decremental.Machine) (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
          (@instHAppendOfAppend.{0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
            (@List.instAppend.{0} DecrAlmostLinearSSSP.Decremental.Machine))
          cs
          (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Machine final
            (@List.nil.{0} DecrAlmostLinearSSSP.Decremental.Machine))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (DecrAlmostLinearSSSP.Decremental.reportVolume cs) (DecrAlmostLinearSSSP.Decremental.reportCount final))) ∧ (∀ (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (k : Nat),
  @Eq.{1} Real ((a.effect s).realReg k)
    (DecrAlmostLinearSSSP.Decremental.Structured.primitiveRealRead a.instruction s k))) ∧ ((∀ (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (k : Nat),
  @Eq.{1} Nat ((a.effect s).natReg k) (DecrAlmostLinearSSSP.Decremental.Structured.primitiveNatRead a.instruction s k)) ∧ (∀ (slot source : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreRequest.natCode slot source) s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.CoreRequest.natResult slot source s)))) ∧ (((∀ (slot source : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreRequest.realCode slot source) s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.CoreRequest.realResult slot source s)) ∧ (∀ (slot source : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    And
      (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CoreRequest.natResult slot source s).natMem
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) slot))
          (s.natReg source)))
      (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CoreRequest.natResult slot source s).realMem s.realMem))) ∧ ((∀ (slot source : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CoreRequest.realResult slot source s).realMem
      (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) slot))
        (s.realReg source)))
    (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CoreRequest.realResult slot source s).natMem s.natMem)) ∧ ((∀ (slot source k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.CoreRequest.natCode slot source) k) ∧ (∀ (slot source k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.CoreRequest.realCode slot source) k))))) ∧ ((((∀ (slot source k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.CoreRequest.natCode slot source) k) ∧ (∀ (slot source k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.CoreRequest.realCode slot source) k)) ∧ ((∀ (N slot source value : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (old : Nat → Nat),
  @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    @Eq.{1} Nat (s.natReg source)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) value) →
      (∀ (j : Nat),
          @LT.lt.{0} Nat instLTNat j N →
            @Eq.{1} Nat
              (s.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (old j))) →
        ∀ (j : Nat),
          @LT.lt.{0} Nat instLTNat j N →
            @Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.CoreRequest.natResult slot source s).natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  ((DecrAlmostLinearSSSP.Decremental.CoreRequest.natResult slot source s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat old slot value j))) ∧ ((∀ (N slot source : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (old : Nat → Real),
  (∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j N →
        @Eq.{1} Real
          (s.realMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
          (old j)) →
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j N →
        @Eq.{1} Real
          ((DecrAlmostLinearSSSP.Decremental.CoreRequest.realResult slot source s).realMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              ((DecrAlmostLinearSSSP.Decremental.CoreRequest.realResult slot source s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
          (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat old slot (s.realReg source) j)) ∧ (∀ (N slot source value : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N g s →
    @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
      @Eq.{1} Nat (s.natReg source)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) value) →
        DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N
          { pc := g.pc, realReg := g.realReg,
            natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat g.natReg slot value,
            realMem := g.realMem, natMem := g.natMem, halted := g.halted, fault := g.fault, work := g.work }
          (DecrAlmostLinearSSSP.Decremental.CoreRequest.natResult slot source s))))) ∧ (((∀ (N slot source : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N g s →
    DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N
      { pc := g.pc,
        realReg := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat g.realReg slot (s.realReg source),
        natReg := g.natReg, realMem := g.realMem, natMem := g.natMem, halted := g.halted, fault := g.fault,
        work := g.work }
      (DecrAlmostLinearSSSP.Decremental.CoreRequest.realResult slot source s)) ∧ (∀ (N entry : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N g s →
    DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N (DecrAlmostLinearSSSP.Decremental.resume g entry) s)) ∧ ((∀ (B slot source : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    (∃ r,
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      ∀ (j : Nat),
        @Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.CoreRequest.natResult slot source s).natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) ∧ ((∀ (B slot source : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  (∃ r,
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
    ∀ (j : Nat),
      @Eq.{1} Real
        ((DecrAlmostLinearSSSP.Decremental.CoreRequest.realResult slot source s).realMem
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (s.realMem
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) ∧ (∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c d : DecrAlmostLinearSSSP.Decremental.Machine} {N : Nat},
  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N c →
    @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code) N →
      DecrAlmostLinearSSSP.Decremental.Ends p c d → DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N d))))))) ∧ ((((((∀ {n k N : Nat} (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (op : DecrAlmostLinearSSSP.Decremental.CutOp n k),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
    DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N c →
      DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p c op)) ∧ (∀ {n k N : Nat} (p : DecrAlmostLinearSSSP.Decremental.Program) (h : DecrAlmostLinearSSSP.Decremental.Physical n k)
  (m : Nat) (ξ cap : Real),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) N →
    DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N (@DecrAlmostLinearSSSP.Decremental.cutInitial n k p h m ξ cap))) ∧ ((∀ (B R N entry : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (g final : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code) N →
      (∃ r,
          @Eq.{1} Nat R
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
        @Eq.{1} Nat g.pc entry →
          @Eq.{1} Bool g.halted Bool.false →
            @Eq.{1} Bool g.fault Bool.false →
              DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail N g →
                DecrAlmostLinearSSSP.Decremental.Ends p g final →
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
                                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) final.work g.work))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N))
                            (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))
                        (And (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N final t)
                          (And
                            (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t final)
                            (∀ (address : Nat),
                              (∀ (a : Nat),
                                  @Ne.{1} Nat address
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) →
                                @Ne.{1} Nat address
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) R
                                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
                                  (∀ (j : Nat),
                                      @LT.lt.{0} Nat instLTNat j N →
                                        @Ne.{1} Nat address
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) R
                                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))) →
                                    And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                      (@Eq.{1} Real (t.realMem address) (s.realMem address))))))) ∧ (∀ (B R N entry : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N (DecrAlmostLinearSSSP.Decremental.resume g entry) s))) ∧ (((∀ (B R N slot source value : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    (∃ r,
        @Eq.{1} Nat R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
        @Eq.{1} Nat (s.natReg source)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) value) →
          DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N
            { pc := g.pc, realReg := g.realReg,
              natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat g.natReg slot value,
              realMem := g.realMem, natMem := g.natMem, halted := g.halted, fault := g.fault, work := g.work }
            (DecrAlmostLinearSSSP.Decremental.CoreRequest.natResult slot source s)) ∧ (∀ (B R N slot source : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    (∃ r,
        @Eq.{1} Nat R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N
        { pc := g.pc,
          realReg := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat g.realReg slot (s.realReg source),
          natReg := g.natReg, realMem := g.realMem, natMem := g.natMem, halted := g.halted, fault := g.fault,
          work := g.work }
        (DecrAlmostLinearSSSP.Decremental.CoreRequest.realResult slot source s))) ∧ ((∀ (tag : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreRequest.tagCode tag) s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.CoreRequest.tagged tag s)) ∧ ((∀ (N tag : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N g s →
    DecrAlmostLinearSSSP.Decremental.CoreRequest.SavedImage N
      { pc := g.pc, realReg := g.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat g.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) tag,
        realMem := g.realMem, natMem := g.natMem, halted := g.halted, fault := g.fault, work := g.work }
      (DecrAlmostLinearSSSP.Decremental.CoreRequest.tagged tag s)) ∧ (∀ (B R N k value : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    @Eq.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) k
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))) →
                DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g
                  { realReg := s.realReg,
                    natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg k value,
                    realMem := s.realMem, natMem := s.natMem }))))) ∧ ((((∀ (B R N k : Nat) (value : Real) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    @Eq.{1} Nat
        (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) k
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g
        { realReg := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg k value,
          natReg := s.natReg, realMem := s.realMem, natMem := s.natMem }) ∧ (∀ (B R N tag : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    (∃ r,
        @Eq.{1} Nat R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N
        { pc := g.pc, realReg := g.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat g.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) tag,
          realMem := g.realMem, natMem := g.natMem, halted := g.halted, fault := g.fault, work := g.work }
        (DecrAlmostLinearSSSP.Decremental.CoreRequest.tagged tag s))) ∧ ((∀ {n k : Nat} (p : DecrAlmostLinearSSSP.Decremental.Program) (g : DecrAlmostLinearSSSP.Decremental.Machine) (e : Fin k),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p g (@DecrAlmostLinearSSSP.Decremental.CutOp.erase n k e))
    (have __src := DecrAlmostLinearSSSP.Decremental.resume g p.update;
    { pc := __src.pc, realReg := __src.realReg,
      natReg :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat g.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) (@Fin.val k e),
      realMem := __src.realMem, natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
      work := __src.work })) ∧ ((∀ {n k : Nat} (p : DecrAlmostLinearSSSP.Decremental.Program) (g : DecrAlmostLinearSSSP.Decremental.Machine) (v : Fin n),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p g (@DecrAlmostLinearSSSP.Decremental.CutOp.queryY n k v))
    (have __src := DecrAlmostLinearSSSP.Decremental.resume g p.update;
    { pc := __src.pc, realReg := __src.realReg,
      natReg :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat g.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) (@Fin.val n v),
      realMem := __src.realMem, natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
      work := __src.work })) ∧ (∀ {n k : Nat} (p : DecrAlmostLinearSSSP.Decremental.Program) (g : DecrAlmostLinearSSSP.Decremental.Machine) (e : Fin k)
  (a b : Fin n) (u : Real),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p g (@DecrAlmostLinearSSSP.Decremental.CutOp.insert n k e a b u))
    (have __src := DecrAlmostLinearSSSP.Decremental.resume g p.update;
    { pc := __src.pc,
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat g.realReg
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) u,
      natReg :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat g.natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) (@Fin.val k e))
            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (@Fin.val n a))
          (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) (@Fin.val n b),
      realMem := __src.realMem, natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
      work := __src.work }))))) ∧ (((∀ {n k : Nat} (p : DecrAlmostLinearSSSP.Decremental.Program) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (a b : Fin n) (delta : Real),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p g
      (@DecrAlmostLinearSSSP.Decremental.CutOp.paired n k a b delta))
    (have __src := DecrAlmostLinearSSSP.Decremental.resume g p.update;
    { pc := __src.pc,
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat g.realReg
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) delta,
      natReg :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat g.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) (@Fin.val n a))
          (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) (@Fin.val n b),
      realMem := __src.realMem, natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
      work := __src.work })) ∧ (∀ (tag k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.CoreRequest.tagCode tag) k)) ∧ ((∀ (tag k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.CoreRequest.tagCode tag) k) ∧ ((∀ {n k : Nat} (B R N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    (∃ r,
        @Eq.{1} Nat R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      ∃ t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRequest.ratioCode s
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) t)
          (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N
            (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p g (@DecrAlmostLinearSSSP.Decremental.CutOp.ratio n k))
            t)) ∧ (∀ {n k : Nat} (B R N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (e : Fin k),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    (∃ r,
        @Eq.{1} Nat R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val k e)) →
        ∃ t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreRequest.eraseCode s
              (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) t)
            (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N
              (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p g
                (@DecrAlmostLinearSSSP.Decremental.CutOp.erase n k e))
              t))))))) ∧ (((((∀ {n k : Nat} (B R N source : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (v : Fin n),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    (∃ r,
        @Eq.{1} Nat R
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) r))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
      @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
        @Ne.{1} Nat source (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
          @Eq.{1} Nat (s.natReg source)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n v)) →
            ∃ t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  (DecrAlmostLinearSSSP.Decremental.CoreRequest.queryCode source) s
                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) t)
                (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N
                  (@DecrAlmostLinearSSSP.Decremental.cutRequest n k p g
                    (@DecrAlmostLinearSSSP.Decremental.CutOp.queryY n k v))
                  t)) ∧ (∀ {l : Nat} (B : Nat) (e f : Fin l) (a c : Nat),
  @LT.lt.{0} Nat instLTNat a (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
    @LT.lt.{0} Nat instLTNat c (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
      @Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.CorePending.address l B e a)
          (@DecrAlmostLinearSSSP.Decremental.CorePending.address l B f c) →
        And (@Eq.{1} (Fin l) e f) (@Eq.{1} Nat a c))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CorePending.prefixCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
    (DecrAlmostLinearSSSP.Decremental.CorePending.prefixData s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.CorePending.prefixData s).natReg
        (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560)))))))
    (And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CorePending.prefixData s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 570) (instOfNatNat (nat_lit 570))))
        (s.natMem
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))))))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.CorePending.prefixData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 572) (instOfNatNat (nat_lit 572))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))
        (∀ (k : Nat),
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 564) (instOfNatNat (nat_lit 564))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 566) (instOfNatNat (nat_lit 566))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))) →
                  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 570) (instOfNatNat (nat_lit 570))) →
                    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 572) (instOfNatNat (nat_lit 572))) →
                      @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.CorePending.prefixData s).natReg k) (s.natReg k))))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CorePending.prefixData s).natMem s.natMem)
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CorePending.prefixData s).realMem s.realMem)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CorePending.insertCode s
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (DecrAlmostLinearSSSP.Decremental.CorePending.inserted s))) ∧ ((∀ {l : Nat} (B : Nat) (xs : List.{0} (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (e : Fin l),
  @DecrAlmostLinearSSSP.Decremental.CorePending.View l B xs s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val l e)) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            ∃ cost t ys,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CorePending.code s
                  cost t)
                (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
                  (And
                    (@Eq.{1} (List.{0} (Fin l)) ys
                      (@ite.{1} (List.{0} (Fin l))
                        (@Membership.mem.{0, 0} (Fin l) (List.{0} (Fin l)) (@List.instMembership.{0} (Fin l)) xs e)
                        (@List.instDecidableMemOfLawfulBEq.{0} (Fin l)
                          (@instBEqOfDecidableEq.{0} (Fin l) (instDecidableEqFin l))
                          (@Std.LawfulBEqOrd.lawfulBEq.{0} (Fin l)
                            (@instBEqOfDecidableEq.{0} (Fin l) (instDecidableEqFin l)) (instOrdFin l)
                            (@Std.LawfulBCmp.toLawfulBEqCmp.{0} (Fin l)
                              (@Preorder.toLE.{0} (Fin l)
                                (@PartialOrder.toPreorder.{0} (Fin l)
                                  (@LinearOrder.toPartialOrder.{0} (Fin l) (@Fin.instLinearOrder l))))
                              (@Preorder.toLT.{0} (Fin l)
                                (@PartialOrder.toPreorder.{0} (Fin l)
                                  (@LinearOrder.toPartialOrder.{0} (Fin l) (@Fin.instLinearOrder l))))
                              (@instBEqOfDecidableEq.{0} (Fin l) (instDecidableEqFin l))
                              (@Ord.compare.{0} (Fin l) (instOrdFin l))
                              (@instLawfulBCmpCompare_mathlib.{0} (Fin l) (@Fin.instLinearOrder l)))
                            (Fin.instLawfulEqOrd l))
                          e xs)
                        xs (@List.cons.{0} (Fin l) e xs)))
                    (And (@DecrAlmostLinearSSSP.Decremental.CorePending.View l B ys t)
                      (And (@LE.le.{0} Nat instLENat (@List.length.{0} (Fin l) ys) l)
                        (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                          (∀ (a : Nat),
                            @Ne.{1} Nat a
                                (@DecrAlmostLinearSSSP.Decremental.CorePending.address l B e
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
                              @Ne.{1} Nat a
                                  (@DecrAlmostLinearSSSP.Decremental.CorePending.address l B e
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                                @Eq.{1} Nat (t.natMem a) (s.natMem a)))))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (e : Fin b.input.k),
  @Eq.{1} Nat
    (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b)
      (@DFunLike.coe.{1, 1, 1}
        (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
        (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
        (@EquivLike.toFunLike.{1, 1, 1}
          (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
            (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
          (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
          (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
            (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
        (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
        (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)))
    (@Fin.val b.input.k e)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b),
  @Eq.{1} Nat
    (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b)
      (@DFunLike.coe.{1, 1, 1}
        (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
        (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
        (@EquivLike.toFunLike.{1, 1, 1}
          (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
            (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
          (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
          (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
            (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
        (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
        (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.k
      (@ite.{1} Nat
        (@LT.lt.{0} Nat instLTNat
          (@Fin.val b.input.n (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
          (@Fin.val b.input.n b.input.source))
        ((@Fin.val b.input.n
              (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)).decLt
          (@Fin.val b.input.n b.input.source))
        (@Fin.val b.input.n (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@Fin.val b.input.n (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.logicalCount b)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (e : DecrAlmostLinearSSSP.Decremental.Edge b) (offset : Nat),
  @Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e offset)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
            (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) offset))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (e f : DecrAlmostLinearSSSP.Decremental.Edge b) (a c : Nat),
  @LT.lt.{0} Nat instLTNat a (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
    @LT.lt.{0} Nat instLTNat c (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
      @Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e a)
          (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B f c) →
        And (@Eq.{1} (DecrAlmostLinearSSSP.Decremental.Edge b) e f) (@Eq.{1} Nat a c)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (v w : Fin b.input.n),
  @Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B v)
      (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B w) →
    @Eq.{1} (Fin b.input.n) v w) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (e : DecrAlmostLinearSSSP.Decremental.Edge b) (offset a : Nat),
  @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e offset)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (v : Fin b.input.n) (a : Nat),
  @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B v)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B offset a : Nat),
  @Ne.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) offset))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (e : DecrAlmostLinearSSSP.Decremental.Edge b) (a : Nat),
  @LT.lt.{0} Nat instLTNat B (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e a)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (v : Fin b.input.n),
  @LT.lt.{0} Nat instLTNat B (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B v)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {e f : DecrAlmostLinearSSSP.Decremental.Edge b},
  @Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e)
      (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b f) →
    @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Edge b) e f)))))))) := by sorry
