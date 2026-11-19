-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_3
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T17:33:37.968869+00:00
-- url     : https://prove2.me/theorems/1d4d590e-1b31-49d7-9f14-71c049d39f13
-- title:
--   Clipped barriers and normalized walk certificates
-- statement:
--   Let the graph, labels, caches, cut states and scalar RAM machines be the objects of the normalized decremental SSSP implementation interface. Each component below is universally quantified over its own parameters and representation hypotheses.
--
--   Clipping thresholds, reciprocal-capacity estimates and cached-label comparisons satisfy the stated inequalities under the core's numerical hypotheses. Normalized source walks and capped distances provide the comparison certificates used by the all-target analysis. The contracts retain real labels and slacks, extended distances, and the exact source and boundary conventions.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_3 : (((((((∀ (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    And
      (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HPow.hPow.{0, 0, 0} Real Int Real
          (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))) K
          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
      (@LE.le.{0} Real Real.instLE
        (@HPow.hPow.{0, 0, 0} Real Int Real
          (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))) K
          (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 1024)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 1024) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1023) (instOfNatNat (nat_lit 1023)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1022) (instOfNatNat (nat_lit 1022)))))))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (p : Fin b.input.n → Real)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (DecrAlmostLinearSSSP.Decremental.capacity b active p e))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (f : DecrAlmostLinearSSSP.Decremental.Edge b → Real)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (t : Real) (v : Fin b.input.n),
  @Eq.{1} Real
    (DecrAlmostLinearSSSP.Decremental.gradient b
      (@Function.update.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (fun a => Real)
        (fun a b_1 =>
          @instDecidableEqSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
            (instDecidableEqFin b.input.k) (DecrAlmostLinearSSSP.Decremental.instDecidableEqReturnVertex b) a b_1)
        f e t)
      v)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (DecrAlmostLinearSSSP.Decremental.gradient b f v)
        (@ite.{1} Real (@Eq.{1} (Fin b.input.n) v (DecrAlmostLinearSSSP.Decremental.tail b e))
          (instDecidableEqFin b.input.n v (DecrAlmostLinearSSSP.Decremental.tail b e))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) t (f e))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
      (@ite.{1} Real (@Eq.{1} (Fin b.input.n) v (DecrAlmostLinearSSSP.Decremental.head b e))
        (instDecidableEqFin b.input.n v (DecrAlmostLinearSSSP.Decremental.head b e))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) t (f e))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (f : DecrAlmostLinearSSSP.Decremental.Edge b → Real)
  (x : Fin b.input.n → Real),
  @Eq.{1} Real (@DecrAlmostLinearSSSP.Decremental.dot b.input.n (DecrAlmostLinearSSSP.Decremental.gradient b f) x)
    (@Neg.neg.{0} Real Real.instNeg
      (∑ e,
        @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (f e)
          (DecrAlmostLinearSSSP.Decremental.incidence b x e)))))) ∧ (((∀ {n k : Nat} (h : DecrAlmostLinearSSSP.Decremental.Physical n k) (C : Finset.{0} (Fin n)) (tau : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) tau →
    @Eq.{1} Real
      (@DecrAlmostLinearSSSP.Decremental.physicalNorm n k h (@DecrAlmostLinearSSSP.Decremental.cutDirection n C tau))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) tau
        (@DecrAlmostLinearSSSP.Decremental.cutCapacity n k h C))) ∧ (∀ {n : Nat} (g : Fin n → Real) (C : Finset.{0} (Fin n)) (tau : Real),
  @Eq.{1} Real (@DecrAlmostLinearSSSP.Decremental.dot n g (@DecrAlmostLinearSSSP.Decremental.cutDirection n C tau))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) tau (∑ v ∈ C, g v)))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b) (x : Fin b.input.n → Real),
  @Eq.{1} Real
    (@DecrAlmostLinearSSSP.Decremental.physicalNorm b.input.n
      (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
        (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
          (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
      (DecrAlmostLinearSSSP.Decremental.cachedPhysical b s) x)
    (DecrAlmostLinearSSSP.Decremental.norm b (@DecrAlmostLinearSSSP.Decremental.State.cache b s) x)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (r : DecrAlmostLinearSSSP.Decremental.CutReply b),
  @Eq.{1} Real
    (DecrAlmostLinearSSSP.Decremental.potential b
      (@DecrAlmostLinearSSSP.Decremental.State.active b (DecrAlmostLinearSSSP.Decremental.toggle b K s r))
      (DecrAlmostLinearSSSP.Decremental.labels b (DecrAlmostLinearSSSP.Decremental.toggle b K s r)))
    (DecrAlmostLinearSSSP.Decremental.potential b (@DecrAlmostLinearSSSP.Decremental.State.active b s) fun v =>
      @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (DecrAlmostLinearSSSP.Decremental.labels b s v)
        (@DecrAlmostLinearSSSP.Decremental.cutDirection b.input.n (@DecrAlmostLinearSSSP.Decremental.CutReply.cut b r)
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@DecrAlmostLinearSSSP.Decremental.CutReply.U b r)))
          v))) ∧ (∀ (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    And
      (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
      (And
        (@LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        (And
          (@LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HPow.hPow.{0, 0, 0} Real Int Real
                (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
          (And
            (@LE.le.{0} Real Real.instLE
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
            (@LE.le.{0} Real Real.instLE
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 8)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 4)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                    (@HPow.hPow.{0, 0, 0} Real Nat Real
                      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 4)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))))))))) ∧ ((((∀ {κ a b : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) κ →
    @LE.le.{0} Real Real.instLE
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (DecrAlmostLinearSSSP.Decremental.clippedLog κ b) (DecrAlmostLinearSSSP.Decremental.clippedLog κ a))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) a b)
        (@Max.max.{0} Real Real.instMax b κ))) ∧ (∀ {κ a d : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) κ →
    @LE.le.{0} Real Real.instLE
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (DecrAlmostLinearSSSP.Decremental.clippedLog κ
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) a d))
          (DecrAlmostLinearSSSP.Decremental.clippedLog κ a))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) d
          (@Max.max.{0} Real Real.instMax a κ)))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) d
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Max.max.{0} Real Real.instMax a κ)
          (@Max.max.{0} Real Real.instMax (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) a d)
            κ))))) ∧ ((∀ {κ a d mu q : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) κ →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) mu →
      @LT.lt.{0} Real Real.instLT q (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
        @LE.le.{0} Real Real.instLE (@abs.{0} Real Real.lattice Real.instAddGroup d)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) q
              (@Max.max.{0} Real Real.instMax a κ)) →
          @LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) mu
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (DecrAlmostLinearSSSP.Decremental.clippedLog κ
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) a d))
                  (DecrAlmostLinearSSSP.Decremental.clippedLog κ a))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) d
                  (@Max.max.{0} Real Real.instMax a κ))))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) mu
                    (@Max.max.{0} Real Real.instMax a κ))
                  (@abs.{0} Real Real.lattice Real.instAddGroup d))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) q))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (p x : Fin b.input.n → Real)
  (q : Real),
  @LT.lt.{0} Real Real.instLT q (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
    @LE.le.{0} Real Real.instLE
        (DecrAlmostLinearSSSP.Decremental.norm b (DecrAlmostLinearSSSP.Decremental.capacity b active p) x) q →
      @LE.le.{0} Real Real.instLE
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (DecrAlmostLinearSSSP.Decremental.potential b active fun v =>
              @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (p v) (x v))
            (DecrAlmostLinearSSSP.Decremental.potential b active p))
          (@DecrAlmostLinearSSSP.Decremental.dot b.input.n
            (DecrAlmostLinearSSSP.Decremental.gradient b (DecrAlmostLinearSSSP.Decremental.capacity b active p)) x))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) q
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) q))))) ∧ (((∀ {n : Nat} (f g : Fin n → Nat) (a z : Fin n),
  @Ne.{1} (Fin n) a z →
    (∀ (v : Fin n), @Ne.{1} (Fin n) v a → @Ne.{1} (Fin n) v z → @Eq.{1} Nat (g v) (f v)) →
      @Eq.{1} Nat (∑ v, g v)
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (∑ v, f v) (g a)) (g z))
            (f a))
          (f z))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  @Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b s)
      (∑ v, DecrAlmostLinearSSSP.Decremental.nonzero (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s v)) →
    @Eq.{1} Nat
      (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b (DecrAlmostLinearSSSP.Decremental.refresh b s e))
      (∑ v,
        DecrAlmostLinearSSSP.Decremental.nonzero
          (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b (DecrAlmostLinearSSSP.Decremental.refresh b s e) v)))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real)
  (choose : DecrAlmostLinearSSSP.Decremental.State b → DecrAlmostLinearSSSP.Decremental.CutReply b)
  (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.Attained b K choose s →
    @Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b s)
      (∑ v, DecrAlmostLinearSSSP.Decremental.nonzero (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s v))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b),
  @Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b s)
      (∑ v, DecrAlmostLinearSSSP.Decremental.nonzero (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s v)) →
    @Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b s)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Eq.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
        (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
          (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
            (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
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
            @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b s) Bool.false →
              @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                  (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
                  (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
                @Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b s)
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                  @LT.lt.{0} Real Real.instLT
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@DecrAlmostLinearSSSP.Decremental.CutReply.G b (choose s))
                        (@DecrAlmostLinearSSSP.Decremental.CutReply.U b (choose s)))
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
                          K)) →
                    @GE.ge.{0} Real Real.instLE
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (DecrAlmostLinearSSSP.Decremental.potential b
                          (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                          (DecrAlmostLinearSSSP.Decremental.labels b s))
                        (DecrAlmostLinearSSSP.Decremental.potential b
                          (@DecrAlmostLinearSSSP.Decremental.State.active b
                            (DecrAlmostLinearSSSP.Decremental.repairStep b K choose s))
                          (DecrAlmostLinearSSSP.Decremental.labels b
                            (DecrAlmostLinearSSSP.Decremental.repairStep b K choose s))))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 8)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            K (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))))) ∧ (((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (DecrAlmostLinearSSSP.Decremental.cacheModel b s e)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b) (e : DecrAlmostLinearSSSP.Decremental.Edge b),
      (∀ (d : DecrAlmostLinearSSSP.Decremental.Edge b),
          @Ne.{1} (DecrAlmostLinearSSSP.Decremental.Edge b) d e →
            @Eq.{1} Real (@DecrAlmostLinearSSSP.Decremental.State.cache b s d)
              (DecrAlmostLinearSSSP.Decremental.cacheModel b s d)) →
        @Eq.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
            (DecrAlmostLinearSSSP.Decremental.gradient b (@DecrAlmostLinearSSSP.Decremental.State.cache b s)) →
          (∀ d ∉ @DecrAlmostLinearSSSP.Decremental.State.pending b s,
              @LT.lt.{0} Real Real.instLT
                (@abs.{0} Real Real.lattice Real.instAddGroup
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@DecrAlmostLinearSSSP.Decremental.State.cache b s d)
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@DecrAlmostLinearSSSP.Decremental.State.y b s (DecrAlmostLinearSSSP.Decremental.tail b d))
                        (@DecrAlmostLinearSSSP.Decremental.State.y b s (DecrAlmostLinearSSSP.Decremental.head b d)))
                      (@DecrAlmostLinearSSSP.Decremental.State.baseline b s d))))
                (@HPow.hPow.{0, 0, 0} Real Int Real
                  (@instHPow.{0, 0} Real Int
                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                  K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))) →
            DecrAlmostLinearSSSP.Decremental.CacheInvariant b K (DecrAlmostLinearSSSP.Decremental.refresh b s e))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    DecrAlmostLinearSSSP.Decremental.CacheInvariant b K (DecrAlmostLinearSSSP.Decremental.initializeState b)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (r : DecrAlmostLinearSSSP.Decremental.CutReply b),
  DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
    DecrAlmostLinearSSSP.Decremental.CacheInvariant b K (DecrAlmostLinearSSSP.Decremental.toggle b K s r)))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b) (e : Fin b.input.k),
      DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
        DecrAlmostLinearSSSP.Decremental.CacheInvariant b K (DecrAlmostLinearSSSP.Decremental.deleteState b s e)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (choose : DecrAlmostLinearSSSP.Decremental.State b → DecrAlmostLinearSSSP.Decremental.CutReply b)
      (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.Attained b K choose s → DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s)) ∧ ((∀ {mu κ old now r : Real},
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) mu →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) κ →
      @LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) mu
                (@Max.max.{0} Real Real.instMax old κ))
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) now old)))
          r →
        And
          (@LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) r)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) mu
                (@Max.max.{0} Real Real.instMax now κ)))
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) mu
              (@Max.max.{0} Real Real.instMax old κ)))
          (@LE.le.{0} Real Real.instLE
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) mu
              (@Max.max.{0} Real Real.instMax old κ))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) r)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) mu
                (@Max.max.{0} Real Real.instMax now κ))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
    @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
        (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
      ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
        And
          (@LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@HPow.hPow.{0, 0, 0} Real Int Real
                  (@instHPow.{0, 0} Real Int
                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                  K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
              (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                (DecrAlmostLinearSSSP.Decremental.labels b s) e))
            (@DecrAlmostLinearSSSP.Decremental.State.cache b s e))
          (@LE.le.{0} Real Real.instLE (@DecrAlmostLinearSSSP.Decremental.State.cache b s e)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@HPow.hPow.{0, 0, 0} Real Int Real
                  (@instHPow.{0, 0} Real Int
                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                  K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
              (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                (DecrAlmostLinearSSSP.Decremental.labels b s) e)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (f g : DecrAlmostLinearSSSP.Decremental.Edge b → Real),
  @Eq.{1} (Fin b.input.n → Real)
    (DecrAlmostLinearSSSP.Decremental.gradient b fun e =>
      @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (f e) (g e))
    fun v =>
    @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (DecrAlmostLinearSSSP.Decremental.gradient b f v) (DecrAlmostLinearSSSP.Decremental.gradient b g v)))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (f g : DecrAlmostLinearSSSP.Decremental.Edge b → Real) (r : Real),
  (∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
      And
        (@LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) r)
            (f e))
          (g e))
        (@LE.le.{0} Real Real.instLE (g e)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) r)
            (f e)))) →
    And
      (∀ (x : Fin b.input.n → Real),
        @LE.le.{0} Real Real.instLE
          (@abs.{0} Real Real.lattice Real.instAddGroup
            (@DecrAlmostLinearSSSP.Decremental.dot b.input.n
              (fun v =>
                @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (DecrAlmostLinearSSSP.Decremental.gradient b f v) (DecrAlmostLinearSSSP.Decremental.gradient b g v))
              x))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) r
            (DecrAlmostLinearSSSP.Decremental.norm b f x)))
      (∀ (x : Fin b.input.n → Real),
        And
          (@LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) r)
              (DecrAlmostLinearSSSP.Decremental.norm b f x))
            (DecrAlmostLinearSSSP.Decremental.norm b g x))
          (@LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.norm b g x)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) r)
              (DecrAlmostLinearSSSP.Decremental.norm b f x))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
    @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
        (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
      And
        (∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
          And
            (@LE.le.{0} Real Real.instLE
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HPow.hPow.{0, 0, 0} Real Int Real
                    (@instHPow.{0, 0} Real Int
                      (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                    K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
                (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                  (DecrAlmostLinearSSSP.Decremental.labels b s) e))
              (@DecrAlmostLinearSSSP.Decremental.State.cache b s e))
            (@LE.le.{0} Real Real.instLE (@DecrAlmostLinearSSSP.Decremental.State.cache b s e)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HPow.hPow.{0, 0, 0} Real Int Real
                    (@instHPow.{0, 0} Real Int
                      (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                    K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
                (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                  (DecrAlmostLinearSSSP.Decremental.labels b s) e))))
        (And
          (∀ (x : Fin b.input.n → Real),
            @LE.le.{0} Real Real.instLE
              (@abs.{0} Real Real.lattice Real.instAddGroup
                (@DecrAlmostLinearSSSP.Decremental.dot b.input.n
                  (fun v =>
                    @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (DecrAlmostLinearSSSP.Decremental.gradient b
                        (DecrAlmostLinearSSSP.Decremental.capacity b
                          (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                          (DecrAlmostLinearSSSP.Decremental.labels b s))
                        v)
                      (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s v))
                  x))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HPow.hPow.{0, 0, 0} Real Int Real
                  (@instHPow.{0, 0} Real Int
                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                  K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                (DecrAlmostLinearSSSP.Decremental.norm b
                  (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                    (DecrAlmostLinearSSSP.Decremental.labels b s))
                  x)))
          (∀ (x : Fin b.input.n → Real),
            And
              (@LE.le.{0} Real Real.instLE
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HPow.hPow.{0, 0, 0} Real Int Real
                      (@instHPow.{0, 0} Real Int
                        (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                      K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
                  (DecrAlmostLinearSSSP.Decremental.norm b
                    (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                      (DecrAlmostLinearSSSP.Decremental.labels b s))
                    x))
                (DecrAlmostLinearSSSP.Decremental.norm b (@DecrAlmostLinearSSSP.Decremental.State.cache b s) x))
              (@LE.le.{0} Real Real.instLE
                (DecrAlmostLinearSSSP.Decremental.norm b (@DecrAlmostLinearSSSP.Decremental.State.cache b s) x)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HPow.hPow.{0, 0, 0} Real Int Real
                      (@instHPow.{0, 0} Real Int
                        (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                      K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))))))
                  (DecrAlmostLinearSSSP.Decremental.norm b
                    (DecrAlmostLinearSSSP.Decremental.capacity b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                      (DecrAlmostLinearSSSP.Decremental.labels b s))
                    x))))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
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
                @GE.ge.{0} Real Real.instLE
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (DecrAlmostLinearSSSP.Decremental.potential b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                      (DecrAlmostLinearSSSP.Decremental.labels b s))
                    (DecrAlmostLinearSSSP.Decremental.potential b
                      (@DecrAlmostLinearSSSP.Decremental.State.active b
                        (DecrAlmostLinearSSSP.Decremental.toggle b K s r))
                      (DecrAlmostLinearSSSP.Decremental.labels b (DecrAlmostLinearSSSP.Decremental.toggle b K s r))))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 8)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (r : DecrAlmostLinearSSSP.Decremental.CutReply b) (reports : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)),
  DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
    DecrAlmostLinearSSSP.Decremental.ReportsComplete b K s r reports →
      DecrAlmostLinearSSSP.Decremental.CacheInvariant b K
        (DecrAlmostLinearSSSP.Decremental.reportedToggle b K s r reports)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
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
                  @GE.ge.{0} Real Real.instLE
                    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                      (DecrAlmostLinearSSSP.Decremental.potential b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                        (DecrAlmostLinearSSSP.Decremental.labels b s))
                      (DecrAlmostLinearSSSP.Decremental.potential b
                        (@DecrAlmostLinearSSSP.Decremental.State.active b
                          (DecrAlmostLinearSSSP.Decremental.reportedToggle b K s r reports))
                        (DecrAlmostLinearSSSP.Decremental.labels b
                          (DecrAlmostLinearSSSP.Decremental.reportedToggle b K s r reports))))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@OfNat.ofNat.{0} Real (nat_lit 8)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  (∀ (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b),
      @Eq.{1} Real
        (@DecrAlmostLinearSSSP.Decremental.State.sample b s
          (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (DecrAlmostLinearSSSP.Decremental.initialLabel b
            (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
          (@DecrAlmostLinearSSSP.Decremental.State.baseline b s
            (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)))) →
    ∀ (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b),
      @Eq.{1} Real
        (@DecrAlmostLinearSSSP.Decremental.State.sample b (DecrAlmostLinearSSSP.Decremental.refresh b s e)
          (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (DecrAlmostLinearSSSP.Decremental.initialLabel b
            (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
          (@DecrAlmostLinearSSSP.Decremental.State.baseline b (DecrAlmostLinearSSSP.Decremental.refresh b s e)
            (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real)
  (choose : DecrAlmostLinearSSSP.Decremental.State b → DecrAlmostLinearSSSP.Decremental.CutReply b)
  (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.Attained b K choose s →
    ∀ (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b),
      @Eq.{1} Real
        (@DecrAlmostLinearSSSP.Decremental.State.sample b s
          (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (DecrAlmostLinearSSSP.Decremental.initialLabel b
            (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
          (@DecrAlmostLinearSSSP.Decremental.State.baseline b s
            (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE
    (@OfNat.ofNat.{0} Real (nat_lit 32)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (DecrAlmostLinearSSSP.Decremental.A b)
      b.input.accuracy)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real)
  (choose : DecrAlmostLinearSSSP.Decremental.State b → DecrAlmostLinearSSSP.Decremental.CutReply b)
  (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.Attained b K choose s →
    DecrAlmostLinearSSSP.Decremental.Stable b s →
      @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
        (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  (∀ (v : Fin b.input.n),
      @Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.State.output b s v)
        (@ite.{1} ENNReal (@Eq.{1} (Fin b.input.n) v b.input.source) (instDecidableEqFin b.input.n v b.input.source)
          (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))
          (DecrAlmostLinearSSSP.Decremental.readout b (@DecrAlmostLinearSSSP.Decremental.State.sample b s v)))) →
    ∀ (v : Fin b.input.n),
      @Eq.{1} ENNReal
        (@DecrAlmostLinearSSSP.Decremental.State.output b (DecrAlmostLinearSSSP.Decremental.refresh b s e) v)
        (@ite.{1} ENNReal (@Eq.{1} (Fin b.input.n) v b.input.source) (instDecidableEqFin b.input.n v b.input.source)
          (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))
          (DecrAlmostLinearSSSP.Decremental.readout b
            (@DecrAlmostLinearSSSP.Decremental.State.sample b (DecrAlmostLinearSSSP.Decremental.refresh b s e) v)))))))))) ∧ ((((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real)
  (choose : DecrAlmostLinearSSSP.Decremental.State b → DecrAlmostLinearSSSP.Decremental.CutReply b)
  (s : DecrAlmostLinearSSSP.Decremental.State b),
  DecrAlmostLinearSSSP.Decremental.Attained b K choose s →
    ∀ (v : Fin b.input.n),
      @Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.State.output b s v)
        (@ite.{1} ENNReal (@Eq.{1} (Fin b.input.n) v b.input.source) (instDecidableEqFin b.input.n v b.input.source)
          (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))
          (DecrAlmostLinearSSSP.Decremental.readout b (@DecrAlmostLinearSSSP.Decremental.State.sample b s v)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (v : Fin b.input.n),
  @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.indegree b v)
    (∑ e,
      @ite.{1} Nat
        (@Eq.{1} (Fin b.input.n) (@DecrAlmostLinearSSSP.Decremental.Digraph.head b.input.n b.input.k b.input.graph e) v)
        (instDecidableEqFin b.input.n
          (@DecrAlmostLinearSSSP.Decremental.Digraph.head b.input.n b.input.k b.input.graph e) v)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Nat instLENat
    (∑ v,
      DecrAlmostLinearSSSP.Decremental.indegree b
        (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
    b.input.k) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE (∑ e, DecrAlmostLinearSSSP.Decremental.coefficient b e)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (DecrAlmostLinearSSSP.Decremental.A b))
      (@Nat.cast.{0} Real Real.instNatCast b.input.size))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (e : Fin b.input.k),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) (DecrAlmostLinearSSSP.Decremental.Q b))
    (DecrAlmostLinearSSSP.Decremental.cost b active
      (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.kappa b)
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (DecrAlmostLinearSSSP.Decremental.Q b))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  @LE.le.{0} Real Real.instLE
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (DecrAlmostLinearSSSP.Decremental.Q b)))
    (DecrAlmostLinearSSSP.Decremental.slack b (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
      (DecrAlmostLinearSSSP.Decremental.initialLabel b) e)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE
    (DecrAlmostLinearSSSP.Decremental.potential b (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
      (DecrAlmostLinearSSSP.Decremental.initialLabel b))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (DecrAlmostLinearSSSP.Decremental.A b))
        (@Nat.cast.{0} Real Real.instNatCast b.input.size))
      (Real.log
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (DecrAlmostLinearSSSP.Decremental.Q b))))) ∧ (∀ {κ a b : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) κ →
    @LE.le.{0} Real Real.instLE a b →
      @LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.clippedLog κ b)
        (DecrAlmostLinearSSSP.Decremental.clippedLog κ a)))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (e : Fin b.input.k)
  (d : DecrAlmostLinearSSSP.Decremental.Edge b),
  @LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.cost b active d)
    (DecrAlmostLinearSSSP.Decremental.cost b (@Finset.erase.{0} (Fin b.input.k) (instDecidableEqFin b.input.k) active e)
      d)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b) (e : Fin b.input.k),
  @LE.le.{0} Real Real.instLE
    (DecrAlmostLinearSSSP.Decremental.potential b
      (@DecrAlmostLinearSSSP.Decremental.State.active b (DecrAlmostLinearSSSP.Decremental.deleteState b s e))
      (DecrAlmostLinearSSSP.Decremental.labels b (DecrAlmostLinearSSSP.Decremental.deleteState b s e)))
    (DecrAlmostLinearSSSP.Decremental.potential b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
      (DecrAlmostLinearSSSP.Decremental.labels b s)))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
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
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (DecrAlmostLinearSSSP.Decremental.potential b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                  (DecrAlmostLinearSSSP.Decremental.labels b s))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@Nat.cast.{0} Real Real.instNatCast (@DecrAlmostLinearSSSP.Decremental.State.toggles b s))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 8)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))
              (DecrAlmostLinearSSSP.Decremental.potential b (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
                (DecrAlmostLinearSSSP.Decremental.initialLabel b))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
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
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    (DecrAlmostLinearSSSP.Decremental.A b))
                  (@Nat.cast.{0} Real Real.instNatCast b.input.size))
                (Real.log
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    (DecrAlmostLinearSSSP.Decremental.Q b))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K (DecrAlmostLinearSSSP.Decremental.initializeState b))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
        ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
          DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K (DecrAlmostLinearSSSP.Decremental.refresh b s e)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
        ∀ (e : Fin b.input.k),
          DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K (DecrAlmostLinearSSSP.Decremental.deleteState b s e))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
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
                    DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K
                      (DecrAlmostLinearSSSP.Decremental.reportedToggle b K s r reports)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
        @LE.le.{0} Real Real.instLE
          (@Nat.cast.{0} Real Real.instNatCast (@DecrAlmostLinearSSSP.Decremental.State.toggles b s))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 16)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))
                  (@HPow.hPow.{0, 0, 0} Real Nat Real
                    (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) K
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (DecrAlmostLinearSSSP.Decremental.A b))
              (@Nat.cast.{0} Real Real.instNatCast b.input.size))
            (Real.log
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                (DecrAlmostLinearSSSP.Decremental.Q b))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
        @LT.lt.{0} Nat instLTNat (@DecrAlmostLinearSSSP.Decremental.State.toggles b s)
          (DecrAlmostLinearSSSP.Decremental.repairLimit b K))))))) ∧ (((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (es : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)),
  @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b s) Bool.false →
    @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
        (@List.cons.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) e es) →
      @Prod.Lex.{0, 0} Nat Nat Nat.lt Nat.lt
        (DecrAlmostLinearSSSP.Decremental.runtimeRepairRank b K (DecrAlmostLinearSSSP.Decremental.refresh b s e))
        (DecrAlmostLinearSSSP.Decremental.runtimeRepairRank b K s)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.RuntimeInvariant b K s →
        @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b s) Bool.false →
          ∀ (r : DecrAlmostLinearSSSP.Decremental.CutReply b)
            (reports : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)),
            @Prod.Lex.{0, 0} Nat Nat Nat.lt Nat.lt
              (DecrAlmostLinearSSSP.Decremental.runtimeRepairRank b K
                (DecrAlmostLinearSSSP.Decremental.reportedToggle b K s r reports))
              (DecrAlmostLinearSSSP.Decremental.runtimeRepairRank b K s))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.State b),
  @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b s) Bool.false →
    @Prod.Lex.{0, 0} Nat Nat Nat.lt Nat.lt
      (DecrAlmostLinearSSSP.Decremental.runtimeRepairRank b K
        (@DecrAlmostLinearSSSP.Decremental.State.mk b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
          (@DecrAlmostLinearSSSP.Decremental.State.y b s) (@DecrAlmostLinearSSSP.Decremental.State.cache b s)
          (@DecrAlmostLinearSSSP.Decremental.State.baseline b s)
          (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
          (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b s)
          (@DecrAlmostLinearSSSP.Decremental.State.sample b s) (@DecrAlmostLinearSSSP.Decremental.State.output b s)
          (@DecrAlmostLinearSSSP.Decremental.State.pending b s) Bool.true
          (@DecrAlmostLinearSSSP.Decremental.State.toggles b s) (@DecrAlmostLinearSSSP.Decremental.State.history b s)))
      (DecrAlmostLinearSSSP.Decremental.runtimeRepairRank b K s)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @WellFounded.{1} (DecrAlmostLinearSSSP.Decremental.State b)
    (@InvImage.{1, 1} (DecrAlmostLinearSSSP.Decremental.State b) (Prod.{0, 0} Nat Nat)
      (@Prod.Lex.{0, 0} Nat Nat Nat.lt Nat.lt) (DecrAlmostLinearSSSP.Decremental.runtimeRepairRank b K))))) ∧ (((∀ {p sample κ mu eps r : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) κ →
    @LT.lt.{0} Real Real.instLT κ p →
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) mu →
        @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eps →
          @LE.le.{0} Real Real.instLE eps (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
            @LE.le.{0} Real Real.instLE
                (@OfNat.ofNat.{0} Real (nat_lit 32)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) mu eps) →
              @LE.le.{0} Real Real.instLE r (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                @LE.le.{0} Real Real.instLE
                    (@abs.{0} Real Real.lattice Real.instAddGroup
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) mu
                          (@Max.max.{0} Real Real.instMax sample κ))
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) p sample)))
                    r →
                  And
                    (@LE.le.{0} Real Real.instLE
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) eps
                            (@OfNat.ofNat.{0} Real (nat_lit 8)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
                        p)
                      sample)
                    (@LE.le.{0} Real Real.instLE sample
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) eps
                            (@OfNat.ofNat.{0} Real (nat_lit 8)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
                        p))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
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
            DecrAlmostLinearSSSP.Decremental.Stable b s →
              ∀ (v : Fin b.input.n),
                @Ne.{1} (Fin b.input.n) v b.input.source →
                  And
                    (@LE.le.{0} Real Real.instLE
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b.input.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 8)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
                        (DecrAlmostLinearSSSP.Decremental.labels b s v))
                      (@DecrAlmostLinearSSSP.Decremental.State.sample b s v))
                    (@LE.le.{0} Real Real.instLE (@DecrAlmostLinearSSSP.Decremental.State.sample b s v)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b.input.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 8)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
                        (DecrAlmostLinearSSSP.Decremental.labels b s v))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (s : DecrAlmostLinearSSSP.Decremental.State b) (x : Fin b.input.n → Real),
  @Eq.{1} Real
    (@DecrAlmostLinearSSSP.Decremental.physicalNorm b.input.n
      (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
        (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
          (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
      (DecrAlmostLinearSSSP.Decremental.cachedPhysical b s) x)
    (DecrAlmostLinearSSSP.Decremental.norm b (@DecrAlmostLinearSSSP.Decremental.State.cache b s) x)) ∧ ((∀ {n : Nat} (g x : Fin n → Real),
  @Eq.{1} Real (@DecrAlmostLinearSSSP.Decremental.dot n g fun v => @Neg.neg.{0} Real Real.instNeg (x v))
    (@Neg.neg.{0} Real Real.instNeg (@DecrAlmostLinearSSSP.Decremental.dot n g x))) ∧ (∀ {n : Nat} (f g x : Fin n → Real),
  @Eq.{1} Real
    (@DecrAlmostLinearSSSP.Decremental.dot n
      (fun v => @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (f v) (g v)) x)
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (@DecrAlmostLinearSSSP.Decremental.dot n f x)
      (@DecrAlmostLinearSSSP.Decremental.dot n g x))))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (f : DecrAlmostLinearSSSP.Decremental.Edge b → Real)
  (x : Fin b.input.n → Real),
  @Eq.{1} Real (DecrAlmostLinearSSSP.Decremental.norm b f fun v => @Neg.neg.{0} Real Real.instNeg (x v))
    (DecrAlmostLinearSSSP.Decremental.norm b f x)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (f : DecrAlmostLinearSSSP.Decremental.Edge b → Real),
  (∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (f e)) →
    ∀ (x : Fin b.input.n → Real),
      @LE.le.{0} Real Real.instLE
        (@abs.{0} Real Real.lattice Real.instAddGroup
          (@DecrAlmostLinearSSSP.Decremental.dot b.input.n (DecrAlmostLinearSSSP.Decremental.gradient b f) x))
        (DecrAlmostLinearSSSP.Decremental.norm b f x))) ∧ ((∀ {K N G U d : Real},
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) N →
      @LE.le.{0} Real Real.instLE
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 4)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
              K))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            G U) →
        @LE.le.{0} Real Real.instLE
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) G U)
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) d N)
              K) →
          @LE.le.{0} Real Real.instLE
            (@HDiv.hDiv.{0, 0, 0} Real Real Real
              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
              (@Neg.neg.{0} Real Real.instNeg N)
              (@OfNat.ofNat.{0} Real (nat_lit 4)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
            d) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
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
            @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
                (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
              Or
                  (@Eq.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
                    (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
                      (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
                        (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero))))
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
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                            K))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@DecrAlmostLinearSSSP.Decremental.CutReply.G b r)
                          (@DecrAlmostLinearSSSP.Decremental.CutReply.U b r)))) →
                DecrAlmostLinearSSSP.Decremental.Balanced b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                  (DecrAlmostLinearSSSP.Decremental.labels b s)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
            (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
          Or
              (@Eq.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b s)
                (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
                  (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
                    (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero))))
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
            DecrAlmostLinearSSSP.Decremental.Balanced b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
              (DecrAlmostLinearSSSP.Decremental.labels b s))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real),
  @LE.le.{0} Real Real.instLE
      (@OfNat.ofNat.{0} Real (nat_lit 32)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
      K →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.State b),
      DecrAlmostLinearSSSP.Decremental.CacheInvariant b K s →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b s)
            (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
          (∀ (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b),
              @Eq.{1} Real
                (@DecrAlmostLinearSSSP.Decremental.State.sample b s
                  (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (DecrAlmostLinearSSSP.Decremental.initialLabel b
                    (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
                  (@DecrAlmostLinearSSSP.Decremental.State.baseline b s
                    (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)))) →
            DecrAlmostLinearSSSP.Decremental.AllTarget b (@DecrAlmostLinearSSSP.Decremental.State.active b s)
                (DecrAlmostLinearSSSP.Decremental.labels b s) →
              ∀ (v : Fin b.input.n),
                @Ne.{1} (Fin b.input.n) v b.input.source →
                  And
                    (@LE.le.{0} Real Real.instLE
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b.input.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 8)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
                        (DecrAlmostLinearSSSP.Decremental.labels b s v))
                      (@DecrAlmostLinearSSSP.Decremental.State.sample b s v))
                    (@LE.le.{0} Real Real.instLE (@DecrAlmostLinearSSSP.Decremental.State.sample b s v)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) b.input.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 8)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))))
                        (DecrAlmostLinearSSSP.Decremental.labels b s v)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (p : Fin b.input.n → Real)
  (e : Fin b.input.k),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
    (DecrAlmostLinearSSSP.Decremental.coreLength b active p e))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (p : Fin b.input.n → Real)
  (e : Fin b.input.k),
  @LE.le.{0} Real Real.instLE
    (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
      (p (@DecrAlmostLinearSSSP.Decremental.Digraph.tail b.input.n b.input.k b.input.graph e))
      (p (@DecrAlmostLinearSSSP.Decremental.Digraph.head b.input.n b.input.k b.input.graph e)))
    (DecrAlmostLinearSSSP.Decremental.coreLength b active p e)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (v : Fin b.input.n),
  @Ne.{1} (Fin b.input.n) v b.input.source →
    @LE.le.{0} ENNReal ENNReal.instLE
      (ENNReal.ofReal
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (DecrAlmostLinearSSSP.Decremental.Q b)))
      (DecrAlmostLinearSSSP.Decremental.coreDistance b active v)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (p : Fin b.input.n → Real),
  @Eq.{1} Real (p b.input.source) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
    ∀ (t : Fin b.input.n) (es : List.{0} (Fin b.input.k)),
      @DecrAlmostLinearSSSP.Decremental.Walk b.input.n b.input.k b.input.graph
          (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k)) b.input.source t es →
        @LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.coreDistance b active t)
          (ENNReal.ofReal
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (p t)
              (@List.sum.{0} Real Real.instAdd Real.instZero
                (@List.map.{0, 0} (Fin b.input.k) Real (DecrAlmostLinearSSSP.Decremental.coreLength b active p) es)))))))))))) := by sorry
