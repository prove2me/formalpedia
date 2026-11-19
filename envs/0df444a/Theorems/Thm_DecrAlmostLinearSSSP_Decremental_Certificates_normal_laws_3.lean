-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_3
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:21:03.763201+00:00
-- url     : https://prove2.me/theorems/b3d2b90c-911b-4101-a1e3-22e51c04f329
-- title:
--   Scale parameters and source-bank initialization
-- statement:
--   Let a source program be a fixed finite deterministic scalar RAM program. Host states contain natural and real registers and memory; scaled instances, cached observations, advancing pointers and dirty queues are the objects defined by the wrapper interface.
--
--   Native doubling and ceiling loops compute the dyadic scale count, scale parameters and rounded barrier weights. Source-bank initialization writes the finite graph tape and parameters for each scaled instance, preserving the other banks and the public answer region. The interpreter respects zero register tails and the allocated register bounds.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_3 : (((((((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.ScaledCeiling.countScales k) ∧ (∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
              DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
                DecrAlmostLinearSSSP.Decremental.ScaledCeiling.countScales k)) ∧ ((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.scaleArea
            k) ∧ (∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.ScaledCeiling.scaleArea k))) ∧ (((∀ (stride k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.Layout.code stride) k) ∧ (∀ (stride k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.Layout.code stride) k)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (DecrAlmostLinearSSSP.Decremental.barrierHigh i)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (e : Fin i.k),
      And
        (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (DecrAlmostLinearSSSP.Decremental.barrierWeight i j e))
        (@LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.barrierWeight i j e)
          (DecrAlmostLinearSSSP.Decremental.barrierHigh i))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid → ∀ (j : Nat), (DecrAlmostLinearSSSP.Decremental.barrierInput i j).Valid))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
      @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@Nat.cast.{0} Real Real.instNatCast i.size))
          i.accuracy →
        ∀ (j : Nat),
          And
            (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (DecrAlmostLinearSSSP.Decremental.barrierInput i j).n)
            (And
              (@LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.barrierInput i j).W
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (DecrAlmostLinearSSSP.Decremental.barrierInput i j).size
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (And
                (@LT.lt.{0} Real Real.instLT
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                    (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.barrierInput i j).size))
                  (DecrAlmostLinearSSSP.Decremental.barrierInput i j).accuracy)
                (@LT.lt.{0} Real Real.instLT (DecrAlmostLinearSSSP.Decremental.barrierInput i j).accuracy
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))) ∧ (∀ (w : Nat) (d : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) d →
    And
      (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast w)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) d
          (@Nat.cast.{0} Real Real.instNatCast
            (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
              (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@Nat.cast.{0} Real Real.instNatCast w) d)))))
      (@LE.le.{0} Real Real.instLE
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) d
          (@Nat.cast.{0} Real Real.instNatCast
            (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
              (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@Nat.cast.{0} Real Real.instNatCast w) d))))
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (@Nat.cast.{0} Real Real.instNatCast w)
          d)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (e : Fin i.k),
      @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (DecrAlmostLinearSSSP.Decremental.scale j)) →
        And
          (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (DecrAlmostLinearSSSP.Decremental.delta i j)
              (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.barrierWeight i j e))))
          (@LE.le.{0} Real Real.instLE
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (DecrAlmostLinearSSSP.Decremental.delta i j)
              (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.barrierWeight i j e)))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@Nat.cast.{0} Real Real.instNatCast (i.weight e)) (DecrAlmostLinearSSSP.Decremental.delta i j)))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (j : Nat) (e : Fin i.k),
      Not
          (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (i.weight e))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 2)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
              (DecrAlmostLinearSSSP.Decremental.scale j))) →
        @LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 4)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
            (DecrAlmostLinearSSSP.Decremental.scale j))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (DecrAlmostLinearSSSP.Decremental.delta i j)
            (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.barrierWeight i j e)))))) ∧ (((∀ (m : Nat),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 512)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 512) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 511) (instOfNatNat (nat_lit 511)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))))))
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (@Nat.cast.{0} Real Real.instNatCast m) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (@HPow.hPow.{0, 0, 0} Real Nat Real
      (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      (DecrAlmostLinearSSSP.Decremental.utilityDepth m))) ∧ (∀ (m : Nat),
  @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.utilityDepth m))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@OfNat.ofNat.{0} Real (nat_lit 12)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 12) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (DecrAlmostLinearSSSP.Decremental.logarithm2
          (@Nat.cast.{0} Real Real.instNatCast
            (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LT.lt.{0} Real Real.instLT
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@Nat.cast.{0} Real Real.instNatCast i.size))
        i.accuracy →
      And
        (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 512)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 512) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 511) (instOfNatNat (nat_lit 511)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))))))
              (@Nat.cast.{0} Real Real.instNatCast i.n))
            i.accuracy))
        (@LE.le.{0} Real Real.instLE
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 512)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 512) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 511) (instOfNatNat (nat_lit 511)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))))))
              (@Nat.cast.{0} Real Real.instNatCast i.n))
            i.accuracy)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size)))) ∧ ((∀ (coefficient stride k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
      @Even.{0} Nat instAddNat k →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
                  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                    (DecrAlmostLinearSSSP.Decremental.Prepass.code coefficient stride) k) ∧ (∀ (coefficient stride k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
              DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
                (DecrAlmostLinearSSSP.Decremental.Prepass.code coefficient stride) k)))))) ∧ (((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast i.size)
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
      ∀ (coefficient stride : Nat),
        ∃ cost t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
              (DecrAlmostLinearSSSP.Decremental.Prepass.code coefficient stride) s cost t)
            (And
              (DecrAlmostLinearSSSP.Decremental.Layout.Represents t
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
                  stride))
              (And
                (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) coefficient
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) i.size
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (And
                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                    (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                  (And
                    (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n
                        (DecrAlmostLinearSSSP.Decremental.scaleCount i)))
                    (And
                      (@LE.le.{0} Nat instLENat cost
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                        DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                      (DecrAlmostLinearSSSP.Decremental.utilityDepth i.size))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (DecrAlmostLinearSSSP.Decremental.dispatchCharge
                                        DecrAlmostLinearSSSP.Decremental.ScaledCeiling.ceilingProgram.code)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                                      (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                              coefficient)
                            stride)
                          (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))))
                      (∀ (address : Nat),
                        (∀ (a : Nat),
                            @Ne.{1} Nat address
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                          And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                            (@Eq.{1} Nat (t.natMem address) (s.natMem address)))))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Fill.body s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) (DecrAlmostLinearSSSP.Decremental.Fill.next s)) ∧ (∀ (n base stride value : Nat) (realValue : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) stride →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116)))) base →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 118) (instOfNatNat (nat_lit 118)))) n →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120)))) stride →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 122) (instOfNatNat (nat_lit 122))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124)))) value →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116)))) realValue →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  ∃ t,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Fill.code s
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) n)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        t)
                      (And
                        (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride n)))
                        (And
                          (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 118) (instOfNatNat (nat_lit 118))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                          (And
                            (∀ (j : Nat),
                              @LT.lt.{0} Nat instLTNat j n →
                                And
                                  (@Eq.{1} Nat
                                    (t.natMem
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride j)))
                                    value)
                                  (@Eq.{1} Real
                                    (t.realMem
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride j)))
                                    realValue))
                            (∀ (address : Nat),
                              (∀ (j : Nat),
                                  @LT.lt.{0} Nat instLTNat j n →
                                    @Ne.{1} Nat address
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) stride j))) →
                                And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                  (@Eq.{1} Real (t.realMem address) (s.realMem address))))))))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 118) (instOfNatNat (nat_lit 118))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Fill.code k) ∧ (∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Fill.code k)) ∧ ((∀ (N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 118) (instOfNatNat (nat_lit 118))))
            N)
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 122) (instOfNatNat (nat_lit 122))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (And
                  (@Eq.{1} Real
                    ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).realReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
                  (@Eq.{1} Nat
                    ((DecrAlmostLinearSSSP.Decremental.SnapshotFill.setupData N s).natReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))))))))) ∧ ((∀ (N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        ∃ t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.SnapshotFill.code N) s
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) N)
                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
              t)
            (And
              (∀ (j : Nat),
                @LT.lt.{0} Nat instLTNat j N →
                  And
                    (@Eq.{1} Nat
                      (t.natMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@Eq.{1} Real
                      (t.realMem
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
              (∀ (address : Nat),
                (∀ (j : Nat),
                    @LT.lt.{0} Nat instLTNat j N →
                      @Ne.{1} Nat address
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))) →
                  And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                    (@Eq.{1} Real (t.realMem address) (s.realMem address))))) ∧ (∀ (N k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 118) (instOfNatNat (nat_lit 118))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 120) (instOfNatNat (nat_lit 120))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 122) (instOfNatNat (nat_lit 122))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 124) (instOfNatNat (nat_lit 124))) →
            DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.SnapshotFill.code N)
              k))))) ∧ ((((∀ (N k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 116) (instOfNatNat (nat_lit 116))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.SnapshotFill.code N) k) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d p x N : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
          (s.realReg x) →
        @LE.le.{0} Real Real.instLE (s.realReg x)
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
                (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productReal d p x) s cost t)
              (And
                (@Eq.{1} Nat (t.natReg d)
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (s.natReg p)
                    (@Nat.ceil.{0} Real Real.semiring Real.partialOrder
                      (@FloorRing.toFloorSemiring.{0} Real Real.instRing Real.linearOrder Real.instFloorRing)
                      (s.realReg x))))
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
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  (And
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
                          (@Eq.{1} Nat (t.natMem address) (s.natMem address)))
                    (∀ (k : Nat),
                      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
                        @Even.{0} Nat instAddNat k →
                          @Ne.{1} Nat k d →
                            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
                              And (@Eq.{1} Nat (t.natReg k) (s.natReg k)) (@Eq.{1} Real (t.realReg k) (s.realReg k)))))))) ∧ ((∀ (d p x k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k d →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productReal d p x) k) ∧ ((∀ (d p x k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
          (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productReal d p x) k) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d p x N : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
      @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (s.natReg x))
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
              (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productNat d p x) s cost t)
            (And
              (@Eq.{1} Nat (t.natReg d)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (s.natReg p) (s.natReg x)))
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
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
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
                      (@Eq.{1} Nat (t.natMem address) (s.natMem address))))))))) ∧ (((∀ (d p x k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k d →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productNat d p x) k) ∧ (∀ (d p x k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
            (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.productNat d p x) k)) ∧ ((∀ (ops : List.{0} (Prod.{0, 0} Nat Nat)) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        (∀ (op : Prod.{0, 0} Nat Nat),
            @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (List.{0} (Prod.{0, 0} Nat Nat))
                (@List.instMembership.{0} (Prod.{0, 0} Nat Nat)) ops op →
              @Ne.{1} Nat k (@Prod.fst.{0, 0} Nat Nat op)) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.batch ops) k) ∧ ((∀ (ops : List.{0} (Prod.{0, 0} Nat Nat)) (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
            (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.batch ops) k) ∧ (∀ (ops : List.{0} (Prod.{0, 0} Nat Nat)) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (N : Nat),
  DecrAlmostLinearSSSP.Decremental.ScaledCeiling.BatchValid ops →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        (∀ (op : Prod.{0, 0} Nat Nat),
            @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (List.{0} (Prod.{0, 0} Nat Nat))
                (@List.instMembership.{0} (Prod.{0, 0} Nat Nat)) ops op →
              @LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast (s.natReg (@Prod.snd.{0, 0} Nat Nat op)))
                (@HPow.hPow.{0, 0, 0} Real Nat Real
                  (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  N)) →
          ∃ cost t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                (DecrAlmostLinearSSSP.Decremental.ScaledCeiling.batch ops) s cost t)
              (And
                (@LE.le.{0} Nat instLENat cost
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@List.length.{0} (Prod.{0, 0} Nat Nat) ops)
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
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))
                (And
                  (∀ (op : Prod.{0, 0} Nat Nat),
                    @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (List.{0} (Prod.{0, 0} Nat Nat))
                        (@List.instMembership.{0} (Prod.{0, 0} Nat Nat)) ops op →
                      @Eq.{1} Nat (t.natReg (@Prod.fst.{0, 0} Nat Nat op))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                          (s.natReg (@Prod.snd.{0, 0} Nat Nat op))))
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
                        (@Eq.{1} Nat (t.natMem address) (s.natMem address)))))))))))) ∧ ((((((DecrAlmostLinearSSSP.Decremental.ScaledCeiling.BatchValid DecrAlmostLinearSSSP.Decremental.ScaleParameters.ordinaryOps) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) i.size →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) i.n →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))) i.k →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
              (@Fin.val i.n i.source) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                (DecrAlmostLinearSSSP.Decremental.bankFactor
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110))))) →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                  ∃ cost t,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                        DecrAlmostLinearSSSP.Decremental.ScaleParameters.ordinary s cost t)
                      (And
                        (@LE.le.{0} Nat instLENat cost
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
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
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 65) (instOfNatNat (nat_lit 65)))))
                        (And
                          (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (DecrAlmostLinearSSSP.Decremental.bankFactor
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                              i.n))
                          (And
                            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 156) (instOfNatNat (nat_lit 156))))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (DecrAlmostLinearSSSP.Decremental.bankFactor
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                i.k))
                            (And
                              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 158) (instOfNatNat (nat_lit 158))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (DecrAlmostLinearSSSP.Decremental.bankFactor
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
                              (And
                                (@Eq.{1} Nat
                                  (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 160) (instOfNatNat (nat_lit 160))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (DecrAlmostLinearSSSP.Decremental.bankFactor
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                    (@Fin.val i.n i.source)))
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
                                      (@Eq.{1} Nat (t.natMem address) (s.natMem address)))))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} Real
      ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.highData s).realReg
        (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 512)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 512) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 511) (instOfNatNat (nat_lit 511)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 510) (instOfNatNat (nat_lit 510)))))))
          (@Nat.cast.{0} Real Real.instNatCast
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66))))))
        (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))))
    (And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.ScaleParameters.highData s).natReg s.natReg)
      (And (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.ScaleParameters.highData s).realMem s.realMem)
        (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.ScaleParameters.highData s).natMem s.natMem)))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LT.lt.{0} Real Real.instLT
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@Nat.cast.{0} Real Real.instNatCast i.size))
        i.accuracy →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) i.n →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) i.accuracy →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
              ∃ cost t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    DecrAlmostLinearSSSP.Decremental.ScaleParameters.high s cost t)
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
                        (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                    (And
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                          (DecrAlmostLinearSSSP.Decremental.barrierHigh i)))
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
                            (@Eq.{1} Nat (t.natMem address) (s.natMem address)))))))) ∧ (((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 204) (instOfNatNat (nat_lit 204))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 156) (instOfNatNat (nat_lit 156))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 158) (instOfNatNat (nat_lit 158))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 160) (instOfNatNat (nat_lit 160))) →
                  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                    DecrAlmostLinearSSSP.Decremental.ScaleParameters.ordinary k) ∧ (∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
            DecrAlmostLinearSSSP.Decremental.ScaleParameters.ordinary k)) ∧ ((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.high k) ∧ ((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 204) (instOfNatNat (nat_lit 204))) →
            DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.high
              k) ∧ (∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 204) (instOfNatNat (nat_lit 204))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 156) (instOfNatNat (nat_lit 156))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 158) (instOfNatNat (nat_lit 158))) →
                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 160) (instOfNatNat (nat_lit 160))) →
                  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))) →
                    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                      DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare k))))) ∧ ((((∀ (k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) k →
    @Even.{0} Nat instAddNat k →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 58) (instOfNatNat (nat_lit 58))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 202) (instOfNatNat (nat_lit 202))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 204) (instOfNatNat (nat_lit 204))) →
              DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
                DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare k) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LT.lt.{0} Real Real.instLT
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@Nat.cast.{0} Real Real.instNatCast i.size))
        i.accuracy →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) i.size →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) i.n →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))) i.k →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                (@Fin.val i.n i.source) →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) i.accuracy →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                    (DecrAlmostLinearSSSP.Decremental.bankFactor
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110))))) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                      ∃ cost t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            DecrAlmostLinearSSSP.Decremental.ScaleParameters.prepare s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
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
                                      (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88)))))
                            (And
                              (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (DecrAlmostLinearSSSP.Decremental.bankFactor
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                  i.n))
                              (And
                                (@Eq.{1} Nat
                                  (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 156) (instOfNatNat (nat_lit 156))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (DecrAlmostLinearSSSP.Decremental.bankFactor
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                    i.k))
                                (And
                                  (@Eq.{1} Nat
                                    (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 158) (instOfNatNat (nat_lit 158))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (DecrAlmostLinearSSSP.Decremental.bankFactor
                                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
                                  (And
                                    (@Eq.{1} Nat
                                      (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 160) (instOfNatNat (nat_lit 160))))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (DecrAlmostLinearSSSP.Decremental.bankFactor
                                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                        (@Fin.val i.n i.source)))
                                    (And
                                      (@Eq.{1} Nat
                                        (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))))
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (DecrAlmostLinearSSSP.Decremental.bankFactor
                                            (s.natReg
                                              (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                          (DecrAlmostLinearSSSP.Decremental.barrierHigh i)))
                                      (∀ (address : Nat),
                                        (∀ (a : Nat),
                                            @Ne.{1} Nat address
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (s.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a))
                                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                                          And (@Eq.{1} Real (t.realMem address) (s.realMem address))
                                            (@Eq.{1} Nat (t.natMem address) (s.natMem address))))))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.ScaleParameters.writeFields s
    (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
    (DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).natMem
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 156) (instOfNatNat (nat_lit 156)))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 158) (instOfNatNat (nat_lit 158)))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152)))))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).natMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 160) (instOfNatNat (nat_lit 160)))))
                (@Eq.{1} Real
                  ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).realMem
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))
                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                    (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
                    (@OfNat.ofNat.{0} Real (nat_lit 16)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      ∀ (address : Nat),
        @Ne.{1} Nat address (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))) →
          @Ne.{1} Nat address
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
            @Ne.{1} Nat address
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) →
              @Ne.{1} Nat address
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
                @Ne.{1} Nat address
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) →
                  And
                    (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).natMem address)
                      (s.natMem address))
                    (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).realMem address)
                      (s.realMem address)))))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 208) (instOfNatNat (nat_lit 208))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.writeFields k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 206) (instOfNatNat (nat_lit 206))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.ScaleParameters.writeFields k)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).realMem
    (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))))
        (@OfNat.ofNat.{0} Real (nat_lit 16)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (i : DecrAlmostLinearSSSP.Decremental.Input)
  (p : DecrAlmostLinearSSSP.Decremental.Program) (scaleIndex F N : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F i.n) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 156) (instOfNatNat (nat_lit 156))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F i.k) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 158) (instOfNatNat (nat_lit 158))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                  (DecrAlmostLinearSSSP.Decremental.barrierHigh i)) →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 160) (instOfNatNat (nat_lit 160))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F (@Fin.val i.n i.source)) →
                @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) i.accuracy →
                  (∀ (j : Nat),
                      @LT.lt.{0} Nat instLTNat j N →
                        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) j →
                          @Eq.{1} Nat
                            (s.natMem
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
                    (∀ (j : Nat),
                        @LT.lt.{0} Nat instLTNat j N →
                          @Eq.{1} Real
                            (s.realMem
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
                      And
                        (∀ (j : Nat),
                          @LT.lt.{0} Nat instLTNat j N →
                            @Eq.{1} Nat
                              ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).natMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                                ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                      (DecrAlmostLinearSSSP.Decremental.barrierInput i scaleIndex)).natReg
                                  j)))
                        (∀ (j : Nat),
                          @LT.lt.{0} Nat instLTNat j N →
                            @Eq.{1} Real
                              ((DecrAlmostLinearSSSP.Decremental.ScaleParameters.fieldData s).realMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)))
                              ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                    (DecrAlmostLinearSSSP.Decremental.barrierInput i scaleIndex)).realReg
                                j))) ∧ (∀ (N : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LT.lt.{0} Real Real.instLT
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@Nat.cast.{0} Real Real.instNatCast i.size))
        i.accuracy →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) N →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) i.size →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) i.n →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))) i.k →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))
                  (@Fin.val i.n i.source) →
                @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) i.accuracy →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112))))
                      (DecrAlmostLinearSSSP.Decremental.bankFactor
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110))))) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                            (∀ (j : Nat),
                                @LT.lt.{0} Nat instLTNat j N →
                                  @LT.lt.{0} Nat instLTNat
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j))
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))) →
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
                                      (@Eq.{1} Nat
                                        (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))))
                                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))))
                                      (And
                                        (@Eq.{1} Nat
                                          (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 154) (instOfNatNat (nat_lit 154))))
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (DecrAlmostLinearSSSP.Decremental.bankFactor
                                              (s.natReg
                                                (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                            i.n))
                                        (And
                                          (@Eq.{1} Nat
                                            (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 152) (instOfNatNat (nat_lit 152))))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (DecrAlmostLinearSSSP.Decremental.bankFactor
                                                (s.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 110) (instOfNatNat (nat_lit 110)))))
                                              (DecrAlmostLinearSSSP.Decremental.barrierHigh i)))
                                          (And
                                            (∀ (j : Nat),
                                              @LT.lt.{0} Nat instLTNat j N →
                                                And
                                                  (@Eq.{1} Nat
                                                    (t.natMem
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (t.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 50)
                                                            (instOfNatNat (nat_lit 50))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          j)))
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (DecrAlmostLinearSSSP.Decremental.bankFactor
                                                        (s.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 110)
                                                            (instOfNatNat (nat_lit 110)))))
                                                      ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                            (DecrAlmostLinearSSSP.Decremental.barrierInput i
                                                              (s.natReg
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 110)
                                                                  (instOfNatNat (nat_lit 110)))))).natReg
                                                        j)))
                                                  (@Eq.{1} Real
                                                    (t.realMem
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (t.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 50)
                                                            (instOfNatNat (nat_lit 50))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          j)))
                                                    ((DecrAlmostLinearSSSP.Decremental.initialMachine p
                                                          (DecrAlmostLinearSSSP.Decremental.barrierInput i
                                                            (s.natReg
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 110)
                                                                (instOfNatNat (nat_lit 110)))))).realReg
                                                      j)))
                                            (∀ (address : Nat),
                                              (∀ (j : Nat),
                                                  @LT.lt.{0} Nat instLTNat j N →
                                                    @Ne.{1} Nat address
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (s.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 50)
                                                            (instOfNatNat (nat_lit 50))))
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          j))) →
                                                (∀ (a : Nat),
                                                    @Ne.{1} Nat address
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (s.natReg
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 48)
                                                              (instOfNatNat (nat_lit 48))))
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))
                                                            a))
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 1)
                                                          (instOfNatNat (nat_lit 1))))) →
                                                  And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                                                    (@Eq.{1} Real (t.realMem address) (s.realMem address)))))))))))))) ∧ (((((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
    (DecrAlmostLinearSSSP.Decremental.registerBound code)) ∧ (∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction
      (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code ins →
    ∀ (j : Nat),
      @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
          (DecrAlmostLinearSSSP.Decremental.instructionRegisters ins) j →
        @LT.lt.{0} Nat instLTNat j (DecrAlmostLinearSSSP.Decremental.registerBound code))) ∧ ((∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (j : Nat),
  DecrAlmostLinearSSSP.Decremental.writesNat ins j →
    @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
      (DecrAlmostLinearSSSP.Decremental.instructionRegisters ins) j) ∧ (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (j : Nat),
  DecrAlmostLinearSSSP.Decremental.writesReal ins j →
    @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
      (DecrAlmostLinearSSSP.Decremental.instructionRegisters ins) j))) ∧ (((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t j : Nat),
  @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code) j →
    @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.execute p c t).natReg j) (c.natReg j)) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t j : Nat),
  @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound p.code) j →
    @Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.execute p c t).realReg j) (c.realReg j))) ∧ ((∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code) c →
    ∀ (t : Nat),
      DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
        (DecrAlmostLinearSSSP.Decremental.execute p c t)) ∧ ((∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c d : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code) c →
    DecrAlmostLinearSSSP.Decremental.Ends p c d →
      DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code) d) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input),
  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
    (DecrAlmostLinearSSSP.Decremental.initialMachine p i)))))) ∧ ((((∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code) c →
    ∀ (e : Nat),
      DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code)
        (DecrAlmostLinearSSSP.Decremental.deletionMachine p c e)) ∧ (∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {i : DecrAlmostLinearSSSP.Decremental.Input} {ds : List.{0} (Fin i.k)}
  {cs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.OnlineRun p i ds cs →
    ∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
      @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Machine
          (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
          (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Machine) cs c →
        DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail (DecrAlmostLinearSSSP.Decremental.registerBound p.code) c)) ∧ ((∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (j : Nat),
  Not (DecrAlmostLinearSSSP.Decremental.writesNat ins j) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.shadowAction ins)
      (DecrAlmostLinearSSSP.Decremental.shadowReg j)) ∧ ((∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (j : Nat),
  Not (DecrAlmostLinearSSSP.Decremental.writesReal ins j) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.shadowAction ins)
      (DecrAlmostLinearSSSP.Decremental.shadowReg j)) ∧ (∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc j : Nat),
  (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
      @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction
          (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code ins →
        Not (DecrAlmostLinearSSSP.Decremental.writesNat ins j)) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.dispatchAux pc code)
      (DecrAlmostLinearSSSP.Decremental.shadowReg j))))) ∧ (((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc j : Nat),
  (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
      @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction
          (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code ins →
        Not (DecrAlmostLinearSSSP.Decremental.writesReal ins j)) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.dispatchAux pc code)
      (DecrAlmostLinearSSSP.Decremental.shadowReg j)) ∧ (∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (bound : Nat),
  Iff (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.registersBelow code bound) Bool.true)
    (∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
      @Membership.mem.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction
          (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@List.instMembership.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code ins →
        ∀ (j : Nat),
          @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
              (DecrAlmostLinearSSSP.Decremental.instructionRegisters ins) j →
            @LT.lt.{0} Nat instLTNat j bound))) ∧ ((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} Bool
    (DecrAlmostLinearSSSP.Decremental.registersBelow code (DecrAlmostLinearSSSP.Decremental.registerBound code))
    Bool.true) ∧ ((∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (bound j : Nat),
  @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.registersBelow code bound) Bool.true →
    @LE.le.{0} Nat instLENat bound j →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.shadowInterpreter code)
        (DecrAlmostLinearSSSP.Decremental.shadowReg j)) ∧ (∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (bound j : Nat),
  @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.registersBelow code bound) Bool.true →
    @LE.le.{0} Nat instLENat bound j →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame (DecrAlmostLinearSSSP.Decremental.shadowInterpreter code)
        (DecrAlmostLinearSSSP.Decremental.shadowReg j))))))))) := by sorry
