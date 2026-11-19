-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_12
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T17:33:28.669225+00:00
-- url     : https://prove2.me/theorems/2dc2decc-e700-4f51-b777-444b90af9ba1
-- title:
--   Cut-input construction and protected machine state
-- statement:
--   Let the graph, labels, caches, cut states and scalar RAM machines be the objects of the normalized decremental SSSP implementation interface. Each component below is universally quantified over its own parameters and representation hypotheses.
--
--   Native boot routines write the physical cut input and its paired demands into the source bank, initialize saved registers and preserve the host records. The constructed source state is the exact finite input required by the dynamic-cut implementation interface. Register, memory and call frames support later repair and deletion executions.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_12 : (((((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CutQualityNative.powered s).natReg s.natReg) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CutQualityNative.powered s).natMem s.natMem)
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CutQualityNative.powered s).realMem s.realMem))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Real
    ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.powered s).realReg
      (@OfNat.ofNat.{0} Nat (nat_lit 418) (instOfNatNat (nat_lit 418))))
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@Nat.cast.{0} Real Real.instNatCast (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 408) (instOfNatNat (nat_lit 408)))))
      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CutQualityNative.rootPower k))) ∧ (((∀ (k : Nat),
  And (@Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 410) (instOfNatNat (nat_lit 410))))
      (And (@Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 412) (instOfNatNat (nat_lit 412))))
        (And (@Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 414) (instOfNatNat (nat_lit 414))))
          (And (@Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 416) (instOfNatNat (nat_lit 416))))
            (@Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 418) (instOfNatNat (nat_lit 418))))))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CutQualityNative.rootPower k) ∧ (∀ (m : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.cutLogHeight m))) ∧ ((∀ (m : Nat),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.cutLogHeight m))
      (Real.log
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      (Real.log
        (@Nat.cast.{0} Real Real.instNatCast
          (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))) ∧ ((∀ (m : Nat),
  @LE.le.{0} Real Real.instLE
    (Real.log
      (@Nat.cast.{0} Real Real.instNatCast
        (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m)))
    (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.cutLogHeight m))) ∧ (∀ (m : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.cutRoot m)))))) ∧ ((((∀ (m : Nat),
  @LT.lt.{0} Nat instLTNat (DecrAlmostLinearSSSP.Decremental.cutLogHeight m)
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
      (DecrAlmostLinearSSSP.Decremental.cutRoot m) (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))) ∧ (∀ (m : Nat),
  @LE.le.{0} Real Real.instLE
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.cutRoot m))
      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 4096)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4096) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 4095) (instOfNatNat (nat_lit 4095)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4094) (instOfNatNat (nat_lit 4094)))))))
      (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.cutLogHeight m))))) ∧ ((∀ (m : Nat),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.cutRoot m))
        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
      (Real.log
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 8192)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 8192) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 8191) (instOfNatNat (nat_lit 8191)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 8190) (instOfNatNat (nat_lit 8190)))))))
      (Real.log
        (@Nat.cast.{0} Real Real.instNatCast
          (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CutQualityNative.heightStart s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.CutQualityNative.heightStarted s)))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CutQualityNative.heightBody s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.CutQualityNative.heightAdvanced s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (m : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) m →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      And
        (DecrAlmostLinearSSSP.Decremental.CutQualityNative.HeightRep m
          (DecrAlmostLinearSSSP.Decremental.CutQualityNative.heightStarted s))
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.heightStarted s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 404) (instOfNatNat (nat_lit 404))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.heightAdvanced s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 402) (instOfNatNat (nat_lit 402))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 402) (instOfNatNat (nat_lit 402))))))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.heightAdvanced s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 404) (instOfNatNat (nat_lit 404))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 404) (instOfNatNat (nat_lit 404))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.heightAdvanced s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 406) (instOfNatNat (nat_lit 406))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 406) (instOfNatNat (nat_lit 406)))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.heightAdvanced s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))))
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.heightAdvanced s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) ∧ ((∀ (m : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      DecrAlmostLinearSSSP.Decremental.CutQualityNative.HeightRep m s →
        (DecrAlmostLinearSSSP.Decremental.Structured.Test.natLess
                (@OfNat.ofNat.{0} Nat (nat_lit 402) (instOfNatNat (nat_lit 402)))
                (@OfNat.ofNat.{0} Nat (nat_lit 406) (instOfNatNat (nat_lit 406)))).holds
            s →
          @LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 404) (instOfNatNat (nat_lit 404))))
            (DecrAlmostLinearSSSP.Decremental.cutLogHeight m)) ∧ (∀ (m : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      DecrAlmostLinearSSSP.Decremental.CutQualityNative.HeightRep m s →
        (DecrAlmostLinearSSSP.Decremental.Structured.Test.natLess
                (@OfNat.ofNat.{0} Nat (nat_lit 402) (instOfNatNat (nat_lit 402)))
                (@OfNat.ofNat.{0} Nat (nat_lit 406) (instOfNatNat (nat_lit 406)))).holds
            s →
          DecrAlmostLinearSSSP.Decremental.CutQualityNative.HeightRep m
            (DecrAlmostLinearSSSP.Decremental.CutQualityNative.heightAdvanced s))))))) ∧ (((((∀ (m : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      DecrAlmostLinearSSSP.Decremental.CutQualityNative.HeightRep m s →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 404) (instOfNatNat (nat_lit 404))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          ∃ t cost,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                DecrAlmostLinearSSSP.Decremental.CutQualityNative.heightLoop s cost t)
              (And (DecrAlmostLinearSSSP.Decremental.CutQualityNative.HeightRep m t)
                (And
                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 404) (instOfNatNat (nat_lit 404))))
                    (DecrAlmostLinearSSSP.Decremental.cutLogHeight m))
                  (@LE.le.{0} Nat instLENat cost
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                        (DecrAlmostLinearSSSP.Decremental.cutLogHeight m))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CutQualityNative.rootBody s
    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
    (DecrAlmostLinearSSSP.Decremental.CutQualityNative.rootAdvanced s))) ∧ ((∀ (t : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CutQualityNative.RootRep t s →
    Iff
      ((DecrAlmostLinearSSSP.Decremental.Structured.Test.realLess
            (@OfNat.ofNat.{0} Nat (nat_lit 418) (instOfNatNat (nat_lit 418)))
            (@OfNat.ofNat.{0} Nat (nat_lit 420) (instOfNatNat (nat_lit 420)))).holds
        s)
      (@LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 408) (instOfNatNat (nat_lit 408))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (Nat.nthRoot (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) t)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.rootAdvanced s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 408) (instOfNatNat (nat_lit 408))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 408) (instOfNatNat (nat_lit 408))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.rootAdvanced s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (And
          (@Eq.{1} Real
            ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.rootAdvanced s).realReg
              (@OfNat.ofNat.{0} Nat (nat_lit 418) (instOfNatNat (nat_lit 418))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@Nat.cast.{0} Real Real.instNatCast
                ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.rootAdvanced s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 408) (instOfNatNat (nat_lit 408)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))
          (@Eq.{1} Real
            ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.rootAdvanced s).realReg
              (@OfNat.ofNat.{0} Nat (nat_lit 420) (instOfNatNat (nat_lit 420))))
            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 420) (instOfNatNat (nat_lit 420)))))))))) ∧ (((∀ (t : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CutQualityNative.RootRep t s →
    (DecrAlmostLinearSSSP.Decremental.Structured.Test.realLess
            (@OfNat.ofNat.{0} Nat (nat_lit 418) (instOfNatNat (nat_lit 418)))
            (@OfNat.ofNat.{0} Nat (nat_lit 420) (instOfNatNat (nat_lit 420)))).holds
        s →
      DecrAlmostLinearSSSP.Decremental.CutQualityNative.RootRep t
        (DecrAlmostLinearSSSP.Decremental.CutQualityNative.rootAdvanced s)) ∧ (∀ (t : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CutQualityNative.RootRep t s →
    ∃ u cost,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CutQualityNative.rootLoop s
          cost u)
        (And (DecrAlmostLinearSSSP.Decremental.CutQualityNative.RootRep t u)
          (And
            (@Eq.{1} Nat (u.natReg (@OfNat.ofNat.{0} Nat (nat_lit 408) (instOfNatNat (nat_lit 408))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (Nat.nthRoot (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) t)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@LE.le.{0} Nat instLENat cost
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (Nat.nthRoot (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) t)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 408) (instOfNatNat (nat_lit 408))))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CutQualityNative.rootStart s
    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (DecrAlmostLinearSSSP.Decremental.CutQualityNative.rootStarted s)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.rootPrefixData s).natReg
        (@OfNat.ofNat.{0} Nat (nat_lit 408) (instOfNatNat (nat_lit 408))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.rootPrefixData s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))))
      (@Eq.{1} Real
        ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.rootPrefixData s).realReg
          (@OfNat.ofNat.{0} Nat (nat_lit 420) (instOfNatNat (nat_lit 420))))
        (@Nat.cast.{0} Real Real.instNatCast
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 404) (instOfNatNat (nat_lit 404))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))))))) ∧ (∀ (t : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 404) (instOfNatNat (nat_lit 404)))) t →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      And
        (DecrAlmostLinearSSSP.Decremental.CutQualityNative.RootRep t
          (DecrAlmostLinearSSSP.Decremental.CutQualityNative.rootStarted s))
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.rootStarted s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 408) (instOfNatNat (nat_lit 408))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) ∧ ((((∀ (N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CutQualityNative.exponentStart N) s
    (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
    (DecrAlmostLinearSSSP.Decremental.CutQualityNative.exponentStarted N s)) ∧ (∀ (N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} Real
      ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.exponentStarted N s).realReg
        (@OfNat.ofNat.{0} Nat (nat_lit 438) (instOfNatNat (nat_lit 438))))
      (@Nat.cast.{0} Real Real.instNatCast
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) N
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 408) (instOfNatNat (nat_lit 408))))
            (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))))))
    (And
      (@Eq.{1} Real
        ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.exponentStarted N s).realReg
          (@OfNat.ofNat.{0} Nat (nat_lit 440) (instOfNatNat (nat_lit 440))))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
      (And
        (@Eq.{1} Real
          ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.exponentStarted N s).realReg
            (@OfNat.ofNat.{0} Nat (nat_lit 442) (instOfNatNat (nat_lit 442))))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        (And
          (@Eq.{1} Real
            ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.exponentStarted N s).realReg
              (@OfNat.ofNat.{0} Nat (nat_lit 444) (instOfNatNat (nat_lit 444))))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
          (@Eq.{1} Real
            ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.exponentStarted N s).realReg
              (@OfNat.ofNat.{0} Nat (nat_lit 446) (instOfNatNat (nat_lit 446))))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CutQualityNative.qualityBody s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.CutQualityNative.qualityAdvanced s)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 444) (instOfNatNat (nat_lit 444))))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 446) (instOfNatNat (nat_lit 446))))
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) →
      And
        (@Eq.{1} Real
          ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.qualityAdvanced s).realReg
            (@OfNat.ofNat.{0} Nat (nat_lit 440) (instOfNatNat (nat_lit 440))))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 440) (instOfNatNat (nat_lit 440))))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))))
        (And
          (@Eq.{1} Real
            ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.qualityAdvanced s).realReg
              (@OfNat.ofNat.{0} Nat (nat_lit 442) (instOfNatNat (nat_lit 442))))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 442) (instOfNatNat (nat_lit 442))))))
          (And
            (@Eq.{1} Real
              ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.qualityAdvanced s).realReg
                (@OfNat.ofNat.{0} Nat (nat_lit 438) (instOfNatNat (nat_lit 438))))
              (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 438) (instOfNatNat (nat_lit 438)))))
            (And
              (@Eq.{1} Real
                ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.qualityAdvanced s).realReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 444) (instOfNatNat (nat_lit 444))))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
              (@Eq.{1} Real
                ((DecrAlmostLinearSSSP.Decremental.CutQualityNative.qualityAdvanced s).realReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 446) (instOfNatNat (nat_lit 446))))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))))) ∧ (∀ (E : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CutQualityNative.QualityRep E s →
    ∃ t cost,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CutQualityNative.qualityLoop
          s cost t)
        (And
          (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 442) (instOfNatNat (nat_lit 442))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              E))
          (@LE.le.{0} Nat instLENat cost
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) E
                  (@Nat.floor.{0} Real Real.semiring Real.partialOrder
                    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                    (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 440) (instOfNatNat (nat_lit 440)))))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))) ∧ (((∀ (N : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NoMemory (DecrAlmostLinearSSSP.Decremental.CutQualityNative.code N)) ∧ (∀ (N m : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) m →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          ∃ t cost,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                (DecrAlmostLinearSSSP.Decremental.CutQualityNative.code N) s cost t)
              (And
                (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 442) (instOfNatNat (nat_lit 442))))
                  (DecrAlmostLinearSSSP.Decremental.computableCutQuality N m))
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                            (DecrAlmostLinearSSSP.Decremental.cutLogHeight m))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                            (DecrAlmostLinearSSSP.Decremental.cutRoot m)))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) N
                            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                              (DecrAlmostLinearSSSP.Decremental.cutRoot m)
                              (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))
                  (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem)))))) ∧ ((∀ (m : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m →
    @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.cutLogHeight m) m) ∧ ((∀ (m : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m →
    And
      (@LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.cutRoot m)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4096) (instOfNatNat (nat_lit 4096))) m))
      (@LE.le.{0} Nat instLENat
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (DecrAlmostLinearSSSP.Decremental.cutRoot m) (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4096) (instOfNatNat (nat_lit 4096))) m))) ∧ (∀ (N m : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) m →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          ∃ t cost,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                (DecrAlmostLinearSSSP.Decremental.CutQualityNative.code N) s cost t)
              (And
                (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 442) (instOfNatNat (nat_lit 442))))
                  (DecrAlmostLinearSSSP.Decremental.computableCutQuality N m))
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 40000) (instOfNatNat (nat_lit 40000)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                      m))
                  (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem))))))))))) ∧ ((((((∀ (N k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 400) (instOfNatNat (nat_lit 400))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 450) (instOfNatNat (nat_lit 450))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.CutQualityNative.code N) k) ∧ (∀ (N k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 400) (instOfNatNat (nat_lit 400))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 450) (instOfNatNat (nat_lit 450))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.CutQualityNative.code N) k)) ∧ ((∀ (N k : Nat),
  @Odd.{0} Nat Nat.instSemiring k →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.CutQualityNative.code N) k) ∧ (∀ (N k : Nat),
  @Odd.{0} Nat Nat.instSemiring k →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.CutQualityNative.code N) k))) ∧ (((∀ (N : Nat) (i : DecrAlmostLinearSSSP.Decremental.Input),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.size →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
        ∃ t cost,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreQuality.code N) s
              cost t)
            (And (DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i t)
              (And
                (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 442) (instOfNatNat (nat_lit 442))))
                  (DecrAlmostLinearSSSP.Decremental.computableCutQuality N
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.size)))
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 80000) (instOfNatNat (nat_lit 80000)))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        i.size)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem)))))) ∧ (∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 500) (instOfNatNat (nat_lit 500))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 540) (instOfNatNat (nat_lit 540))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreParameters.finish k)) ∧ ((∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 500) (instOfNatNat (nat_lit 500))))
      (Or (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 540) (instOfNatNat (nat_lit 540))) k)
        (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 500) (instOfNatNat (nat_lit 500))))
          (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 502) (instOfNatNat (nat_lit 502)))))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreParameters.finish k) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i
      (DecrAlmostLinearSSSP.Decremental.CoreParameters.finished s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreCeiling.start s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.CoreCeiling.started s)))))) ∧ ((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreCeiling.body s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.CoreCeiling.advanced s)) ∧ (∀ (x : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 522) (instOfNatNat (nat_lit 522)))) x →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      And (DecrAlmostLinearSSSP.Decremental.CoreCeiling.Rep x (DecrAlmostLinearSSSP.Decremental.CoreCeiling.started s))
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.CoreCeiling.started s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 526) (instOfNatNat (nat_lit 526))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CoreCeiling.advanced s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 526) (instOfNatNat (nat_lit 526))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 526) (instOfNatNat (nat_lit 526))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (And
        (@Eq.{1} Real
          ((DecrAlmostLinearSSSP.Decremental.CoreCeiling.advanced s).realReg
            (@OfNat.ofNat.{0} Nat (nat_lit 526) (instOfNatNat (nat_lit 526))))
          (@Nat.cast.{0} Real Real.instNatCast
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 526) (instOfNatNat (nat_lit 526))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (And
          (@Eq.{1} Real
            ((DecrAlmostLinearSSSP.Decremental.CoreCeiling.advanced s).realReg
              (@OfNat.ofNat.{0} Nat (nat_lit 522) (instOfNatNat (nat_lit 522))))
            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 522) (instOfNatNat (nat_lit 522)))))
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.CoreCeiling.advanced s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ ((∀ (x : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreCeiling.Rep x s →
    ∃ t cost,
      And (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreCeiling.loop s cost t)
        (And
          (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 526) (instOfNatNat (nat_lit 526))))
            (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
              (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) x))
          (And
            (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 526) (instOfNatNat (nat_lit 526))))
              (@Nat.cast.{0} Real Real.instNatCast
                (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                  (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) x)))
            (@LE.le.{0} Nat instLENat cost
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                    (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                      (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) x)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 526) (instOfNatNat (nat_lit 526))))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))) ∧ (∀ (x : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 522) (instOfNatNat (nat_lit 522)))) x →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      ∃ t cost,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
            (DecrAlmostLinearSSSP.Decremental.CoreCeiling.start.seq DecrAlmostLinearSSSP.Decremental.CoreCeiling.loop) s
            cost t)
          (And
            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 526) (instOfNatNat (nat_lit 526))))
              (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) x))
            (And
              (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 526) (instOfNatNat (nat_lit 526))))
                (@Nat.cast.{0} Real Real.instNatCast
                  (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                    (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) x)))
              (@LE.le.{0} Nat instLENat cost
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                    (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                      (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing) x))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))))))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 526) (instOfNatNat (nat_lit 526))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.CoreCeiling.start.seq DecrAlmostLinearSSSP.Decremental.CoreCeiling.loop) k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 526) (instOfNatNat (nat_lit 526))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
      (DecrAlmostLinearSSSP.Decremental.CoreCeiling.start.seq DecrAlmostLinearSSSP.Decremental.CoreCeiling.loop) k)) ∧ ((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory
  (DecrAlmostLinearSSSP.Decremental.CoreCeiling.start.seq DecrAlmostLinearSSSP.Decremental.CoreCeiling.loop)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 442) (instOfNatNat (nat_lit 442)))) K →
      ∃ t cost,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreParameters.code s cost
            t)
          (And (DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input t)
            (And (DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K t)
              (And
                (@LE.le.{0} Nat instLENat cost
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
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
                          b.input.accuracy)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 45) (instOfNatNat (nat_lit 45)))))
                (And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem)))))) ∧ (∀ (N : Nat),
  @Eq.{1} Bool
    (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters
      (DecrAlmostLinearSSSP.Decremental.CoreInitialize.registerCode N))
    Bool.true)))))) ∧ (((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  ∃ cost t,
    And
      (DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.CoreInitialize.registerCode N)
        (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine p b.input))
        cost t)
      (And
        (@LE.le.{0} Nat instLENat cost
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 80000) (instOfNatNat (nat_lit 80000)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
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
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                      (DecrAlmostLinearSSSP.Decremental.logarithm2
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@Nat.cast.{0} Real Real.instNatCast b.input.size)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                    b.input.accuracy))))
            (@OfNat.ofNat.{0} Nat (nat_lit 86) (instOfNatNat (nat_lit 86)))))
        (And (DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input t)
          (And
            (DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b
              (DecrAlmostLinearSSSP.Decremental.computableCutQuality N
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size))
              t)
            (And
              (DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                t)
              (And
                (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 546) (instOfNatNat (nat_lit 546))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (And
                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (And
                    (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    (And
                      (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 520) (instOfNatNat (nat_lit 520))))
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
                            (DecrAlmostLinearSSSP.Decremental.computableCutQuality N
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)))))
                      (And
                        (@Eq.{1} (Nat → Nat) t.natMem
                          (DecrAlmostLinearSSSP.Decremental.initialMachine p b.input).natMem)
                        (And
                          (@Eq.{1} (Nat → Real) t.realMem
                            (DecrAlmostLinearSSSP.Decremental.initialMachine p b.input).realMem)
                          (∀ (j : Nat),
                            And
                              (@Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (@Eq.{1} Real (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))))))))))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
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
        (DecrAlmostLinearSSSP.Decremental.CoreInitialize.bootRecordsCode N)
        (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine p b.input))
        cost t)
      (And
        (@LE.le.{0} Nat instLENat cost
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 80000) (instOfNatNat (nat_lit 80000)))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) N
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 180) (instOfNatNat (nat_lit 180))))
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
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
                      (DecrAlmostLinearSSSP.Decremental.logarithm2
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@Nat.cast.{0} Real Real.instNatCast b.input.size)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))
                    b.input.accuracy))))
            (@OfNat.ofNat.{0} Nat (nat_lit 86) (instOfNatNat (nat_lit 86)))))
        (And
          (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K (DecrAlmostLinearSSSP.Decremental.initializeState b) t)
          (And
            (∀ (j : Nat),
              And
                (@Eq.{1} Nat
                  (t.natMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (@Eq.{1} Real
                  (t.realMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
            (And
              (@Eq.{1} Nat
                (t.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B)
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (∀ (j : Nat),
                And
                  (@Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Eq.{1} Real (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))))))))) ∧ ((∀ (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (address : Nat),
  @Eq.{1} Nat ((a.effect s).natMem address)
    (DecrAlmostLinearSSSP.Decremental.Structured.primitiveNatMemory a.instruction s address)) ∧ (∀ (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (address : Nat),
  @Eq.{1} Real ((a.effect s).realMem address)
    (DecrAlmostLinearSSSP.Decremental.Structured.primitiveRealMemory a.instruction s address)))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
    (DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s)) ∧ (∀ (B e : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 690) (instOfNatNat (nat_lit 690))))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
          @Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s).natMem
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) e))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) e))
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) e))
                (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) ∧ ((∀ (B e : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        @Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s).realMem
          (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) e))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600)))))) ∧ ((∀ (e : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      @Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) e
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
    Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 680) (instOfNatNat (nat_lit 680))))
        (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 690) (instOfNatNat (nat_lit 690))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 692) (instOfNatNat (nat_lit 692))) k)) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.code k))))) ∧ ((((∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.code k) ∧ (∀ (B e : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 690) (instOfNatNat (nat_lit 690))))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
          And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s).natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) e))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s).natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) e))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))))))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s).natMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) e))
                      (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Eq.{1} Real
                  ((DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s).realMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) e))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))))))))) ∧ ((∀ (B e : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 690) (instOfNatNat (nat_lit 690))))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
          ∀ (j : Nat),
            @Ne.{1} Nat j
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) e))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
              @Ne.{1} Nat j
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) e))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
                @Ne.{1} Nat j
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) e))
                      (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))) →
                  @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s).natMem j) (s.natMem j)) ∧ ((∀ (B e : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
        ∀ (j : Nat),
          @Ne.{1} Nat j
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) e))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
            @Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s).realMem j) (s.realMem j)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B e : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) e) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 690) (instOfNatNat (nat_lit 690))))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
            DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state
              (DecrAlmostLinearSSSP.Decremental.CoreGuestEdge.result s))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
    (DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.result s)) ∧ (∀ (B G l v : Nat) (gamma : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554)))) G →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 542) (instOfNatNat (nat_lit 542))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) l) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) v →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
            @Eq.{1} Real
                (s.realMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) G
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v)))
                gamma →
              @Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.result s).realMem
                (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l v)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  gamma))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.result s).natMem s.natMem) ∧ ((∀ (v : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) v →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.result s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) v
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))) →
    Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 680) (instOfNatNat (nat_lit 680))))
        (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 684) (instOfNatNat (nat_lit 684))) k) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGuestGamma.code k)))))))) := by sorry
