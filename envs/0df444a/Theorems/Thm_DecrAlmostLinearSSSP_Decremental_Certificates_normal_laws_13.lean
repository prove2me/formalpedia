-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_normal_laws_13
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_13
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:20:44.404202+00:00
-- url     : https://prove2.me/theorems/8e056d87-460c-4de7-97fa-314581adf02c
-- title:
--   Uniform normal-domain program and charged work
-- statement:
--   Let a source program be a fixed finite deterministic scalar RAM program. Host states contain natural and real registers and memory; scaled instances, cached observations, advancing pointers and dirty queues are the objects defined by the wrapper interface.
--
--   The fixed normal-domain program terminates after initialization and every legal deletion prefix, maintains simultaneous approximate distances and exact unreachability, and supports nine-instruction stored-array queries. Its total charged work is bounded by a positive program-dependent constant times a positive subpolynomial overhead, the size bound, inverse accuracy and the saturated weight logarithm. The contracts include the actual online-run coupling and the final concrete-program maintenance theorem, rather than assuming an accurate output array as input.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.normal_laws_13 : ((((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B reserve : Nat}
  {f : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine}
  {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal} {ptr : Fin i.n → Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve f b ptr s →
    ∀ (e : Nat),
      DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve f b ptr
        (DecrAlmostLinearSSSP.Decremental.Native.externalInput s e)) ∧ (∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (e : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data
    (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.deletionMachine host c e))
    (DecrAlmostLinearSSSP.Decremental.Native.externalInput (DecrAlmostLinearSSSP.Decremental.Structured.data c) e))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
      @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@Nat.cast.{0} Real Real.instNatCast i.size))
          i.accuracy →
        ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (queryBound coefficient : Nat),
          (∀ (x : DecrAlmostLinearSSSP.Decremental.Input),
              x.Valid →
                @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x.n →
                  @LE.le.{0} Nat instLENat x.W
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) x.size
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                    @LT.lt.{0} Real Real.instLT
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@Nat.cast.{0} Real Real.instNatCast x.size))
                        x.accuracy →
                      @LT.lt.{0} Real Real.instLT x.accuracy
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                        DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false x) →
            ∃ f cost c,
              And
                (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                  DecrAlmostLinearSSSP.Decremental.Native.InitialFacts p C a i
                    (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q) (f q))
                (And
                  (DecrAlmostLinearSSSP.Decremental.Ends
                    (DecrAlmostLinearSSSP.Decremental.Native.normalProgram coefficient p)
                    (DecrAlmostLinearSSSP.Decremental.initialMachine
                      (DecrAlmostLinearSSSP.Decremental.Native.normalProgram coefficient p) i)
                    c)
                  (And
                    (@Eq.{1} Nat c.work
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) cost
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (And
                      (@LE.le.{0} Nat instLENat cost
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.Native.setupCost i coefficient
                                (DecrAlmostLinearSSSP.Decremental.registerBound p.code))
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (DecrAlmostLinearSSSP.Decremental.dispatchCharge p.code)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (@DecrAlmostLinearSSSP.Decremental.Native.maxInitialWork i f))
                                    (DecrAlmostLinearSSSP.Decremental.Native.initOverhead i p))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                                (DecrAlmostLinearSSSP.Decremental.scaleCount i)))
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                  (DecrAlmostLinearSSSP.Decremental.scaleCount i))
                                (@OfNat.ofNat.{0} Nat (nat_lit 48) (instOfNatNat (nat_lit 48))))
                              i.n))
                          (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))
                      (And
                        (DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) coefficient
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                i.size (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          f (fun q v => DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                          (DecrAlmostLinearSSSP.Decremental.Native.initialPointers i fun q v =>
                            DecrAlmostLinearSSSP.Decremental.stored (f q) (@Fin.val i.n v))
                          (DecrAlmostLinearSSSP.Decremental.Structured.data c))
                        (∀ (v : Fin i.n),
                          And
                            (@LE.le.{0} ENNReal ENNReal.instLE (i.dist (@List.nil.{0} (Fin i.k)) v)
                              (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val i.n v)))
                            (And
                              (@LE.le.{0} ENNReal ENNReal.instLE
                                (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val i.n v))
                                (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                                  (@instHMul.{0} ENNReal
                                    (@Distrib.toMul.{0} ENNReal
                                      (@instDistribOfSemiring.{0} ENNReal
                                        (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                                  (ENNReal.ofReal
                                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                      i.accuracy))
                                  (i.dist (@List.nil.{0} (Fin i.k)) v)))
                              (Iff
                                (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored c (@Fin.val i.n v))
                                  (@Top.top.{0} ENNReal ENNReal.instTop))
                                (Not
                                  (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph
                                    (@DecrAlmostLinearSSSP.Decremental.live i.k (@List.nil.{0} (Fin i.k))) i.source
                                    v)))))))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (coefficient B reserve : Nat),
      @LE.le.{0} Nat instLENat i.n B →
        ∀ (e : Fin i.k)
          (before after :
            Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
          (b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal) (ptr : Fin i.n → Nat)
          (c : DecrAlmostLinearSSSP.Decremental.Machine),
          DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve before b ptr
              (DecrAlmostLinearSSSP.Decremental.Structured.data c) →
            (∀ (v : Fin i.n), DecrAlmostLinearSSSP.Decremental.PointerValid i b v (ptr v)) →
              (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                  DecrAlmostLinearSSSP.Decremental.ZeroRegisterTail
                    (DecrAlmostLinearSSSP.Decremental.registerBound p.code) (before q)) →
                (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                    DecrAlmostLinearSSSP.Decremental.Ends p
                      (DecrAlmostLinearSSSP.Decremental.deletionMachine p (before q) (@Fin.val i.k e)) (after q)) →
                  (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
                      @LE.le.{0} Nat instLENat (after q).work reserve) →
                    (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
                        And
                          (@LE.le.{0} Nat instLENat ((after q).natMem (@Fin.val i.n v))
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          (@Eq.{1} Nat ((after q).natMem (@Fin.val i.n v))
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                            @LE.le.{0} Real Real.instLE
                              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                              ((after q).realMem (@Fin.val i.n v)))) →
                      have initial := DecrAlmostLinearSSSP.Decremental.Native.boundaryAdapter i b ptr;
                      have final :=
                        DecrAlmostLinearSSSP.Decremental.adapterTrace i initial
                          (DecrAlmostLinearSSSP.Decremental.Native.updateEventsPrefix i p B e before after
                            (DecrAlmostLinearSSSP.Decremental.scaleCount i));
                      ∃ d,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Ends
                            (DecrAlmostLinearSSSP.Decremental.Native.normalProgram coefficient p)
                            (DecrAlmostLinearSSSP.Decremental.deletionMachine
                              (DecrAlmostLinearSSSP.Decremental.Native.normalProgram coefficient p) c (@Fin.val i.k e))
                            d)
                          (And
                            (DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve after
                              (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i final)
                              (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i final)
                              (DecrAlmostLinearSSSP.Decremental.Structured.data d))
                            (@LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d.work
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                  (DecrAlmostLinearSSSP.Decremental.pointerEnergy i initial)))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (DecrAlmostLinearSSSP.Decremental.Native.scaleUpdateCharge p i.size)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 36) (instOfNatNat (nat_lit 36))))
                                      (DecrAlmostLinearSSSP.Decremental.Native.updateWorkPrefix i before after
                                        (DecrAlmostLinearSSSP.Decremental.scaleCount i))))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                    (DecrAlmostLinearSSSP.Decremental.pointerEnergy i final)))
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) ∧ (((∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real} {a : Nat → Real} {queryBound : Nat}
  {i : DecrAlmostLinearSSSP.Decremental.Input},
  DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false i →
    ∀ (ds : List.{0} (Fin i.k)),
      @DecrAlmostLinearSSSP.Decremental.Legal i.k ds →
        Nonempty.{1} (DecrAlmostLinearSSSP.Decremental.SourceGuide p C a i ds)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (upper : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
  (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
      @LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a j v) (upper j v)) →
    ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (value : ENNReal),
      @LE.le.{0} ENNReal ENNReal.instLE value (upper j v) →
        ∀ (k : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (z : Fin i.n),
          @LE.le.{0} ENNReal ENNReal.instLE
            (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
              (DecrAlmostLinearSSSP.Decremental.adapterWrite i a j v value) k z)
            (upper k z))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (upper : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
  (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
      @LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a j v) (upper j v)) →
    ∀ (xs : List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i)),
      (∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (value : ENNReal),
          @Membership.mem.{0, 0}
              (Prod.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal))
              (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
              (@List.instMembership.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i)) xs
              (@Prod.mk.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal) j
                (@Prod.mk.{0, 0} (Fin i.n) ENNReal v value)) →
            @LE.le.{0} ENNReal ENNReal.instLE value (upper j v)) →
        ∀ (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
          @LE.le.{0} ENNReal ENNReal.instLE
            (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
              (DecrAlmostLinearSSSP.Decremental.adapterTrace i a xs) j v)
            (upper j v)) ∧ ((∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {c d : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Ends p c d →
    @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
      (DecrAlmostLinearSSSP.Decremental.execute p c
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) d.work c.work))
      d) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (B : Nat) (e : Fin i.k)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
  (j q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (value : ENNReal),
  @Membership.mem.{0, 0}
      (Prod.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal))
      (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
      (@List.instMembership.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
      (DecrAlmostLinearSSSP.Decremental.Native.scaleEvents i p B e before after j)
      (@Prod.mk.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal) q
        (@Prod.mk.{0, 0} (Fin i.n) ENNReal v value)) →
    @Eq.{1} ENNReal value (DecrAlmostLinearSSSP.Decremental.stored (after q) (@Fin.val i.n v))))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (B : Nat) (e : Fin i.k)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
  (d : Nat) (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n) (value : ENNReal),
  @Membership.mem.{0, 0}
      (Prod.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal))
      (List.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
      (@List.instMembership.{0} (DecrAlmostLinearSSSP.Decremental.AdapterEvent i))
      (DecrAlmostLinearSSSP.Decremental.Native.updateEventsPrefix i p B e before after d)
      (@Prod.mk.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (Prod.{0, 0} (Fin i.n) ENNReal) q
        (@Prod.mk.{0, 0} (Fin i.n) ENNReal v value)) →
    @Eq.{1} ENNReal value (DecrAlmostLinearSSSP.Decremental.stored (after q) (@Fin.val i.n v))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (B : Nat) (e : Fin i.k)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
  (a : DecrAlmostLinearSSSP.Decremental.AdapterState i)
  (upper : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal),
  (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
      @LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a q v) (upper q v)) →
    (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
        @LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.stored (after q) (@Fin.val i.n v))
          (upper q v)) →
      ∀ (d : Nat) (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
        @LE.le.{0} ENNReal ENNReal.instLE
          (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
            (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
              (DecrAlmostLinearSSSP.Decremental.Native.updateEventsPrefix i p B e before after d))
            q v)
          (upper q v))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (B : Nat) (e : Fin i.k)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
  (a : DecrAlmostLinearSSSP.Decremental.AdapterState i) (j : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
  DecrAlmostLinearSSSP.Decremental.Ends p
      (DecrAlmostLinearSSSP.Decremental.deletionMachine p (before j) (@Fin.val i.k e)) (after j) →
    (∀ (v : Fin i.n),
        @LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.stored (before j) (@Fin.val i.n v))
          (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a j v)) →
      ∀ (v : Fin i.n),
        @LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.stored (after j) (@Fin.val i.n v))
          (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
            (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
              (DecrAlmostLinearSSSP.Decremental.Native.scaleEvents i p B e before after j))
            j v)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (B : Nat) (e : Fin i.k)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
  (a : DecrAlmostLinearSSSP.Decremental.AdapterState i),
  (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
      DecrAlmostLinearSSSP.Decremental.Ends p
        (DecrAlmostLinearSSSP.Decremental.deletionMachine p (before q) (@Fin.val i.k e)) (after q)) →
    (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
        @LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.stored (before q) (@Fin.val i.n v))
          (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a q v)) →
      ∀ (d : Nat) (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
        @LT.lt.{0} Nat instLTNat (@Fin.val (DecrAlmostLinearSSSP.Decremental.scaleCount i) q) d →
          ∀ (v : Fin i.n),
            @LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.stored (after q) (@Fin.val i.n v))
              (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
                (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
                  (DecrAlmostLinearSSSP.Decremental.Native.updateEventsPrefix i p B e before after d))
                q v)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (B : Nat) (e : Fin i.k)
  (before after : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → DecrAlmostLinearSSSP.Decremental.Machine)
  (a : DecrAlmostLinearSSSP.Decremental.AdapterState i),
  (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
      DecrAlmostLinearSSSP.Decremental.Ends p
        (DecrAlmostLinearSSSP.Decremental.deletionMachine p (before q) (@Fin.val i.k e)) (after q)) →
    (∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
        @LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.stored (before q) (@Fin.val i.n v))
          (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i a q v)) →
      ∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
        @LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.stored (after q) (@Fin.val i.n v))
          (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i
            (DecrAlmostLinearSSSP.Decremental.adapterTrace i a
              (DecrAlmostLinearSSSP.Decremental.Native.updateEventsPrefix i p B e before after
                (DecrAlmostLinearSSSP.Decremental.scaleCount i)))
            q v))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
      @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@Nat.cast.{0} Real Real.instNatCast i.size))
          i.accuracy →
        ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (queryBound : Nat),
          (∀ (x : DecrAlmostLinearSSSP.Decremental.Input),
              x.Valid →
                @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x.n →
                  @LE.le.{0} Nat instLENat x.W
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) x.size
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                    @LT.lt.{0} Real Real.instLT
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@Nat.cast.{0} Real Real.instNatCast x.size))
                        x.accuracy →
                      @LT.lt.{0} Real Real.instLT x.accuracy
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                        DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false x) →
            ∀ (ds : List.{0} (Fin i.k)),
              @DecrAlmostLinearSSSP.Decremental.Legal i.k ds →
                Nonempty.{1} (DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds)) ∧ (∀ {k : Nat} (ds : List.{0} (Fin k)) (r t : Nat),
  @LE.le.{0} Nat instLENat t r →
    @LE.le.{0} (Finset.{0} (Fin k))
      (@Preorder.toLE.{0} (Finset.{0} (Fin k))
        (@PartialOrder.toPreorder.{0} (Finset.{0} (Fin k)) (@Finset.instPartialOrder.{0} (Fin k))))
      (@DecrAlmostLinearSSSP.Decremental.live k (@List.take.{0} (Fin k) r ds))
      (@DecrAlmostLinearSSSP.Decremental.live k (@List.take.{0} (Fin k) t ds)))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input},
  i.Valid →
    ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real} {a : Nat → Real} {ds : List.{0} (Fin i.k)}
      {guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds}
      {t :
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
      {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal} {ptr : Fin i.n → Nat},
      @DecrAlmostLinearSSSP.Decremental.Native.HistoryBoundary i p C a ds guides t b ptr →
        ∀ (v : Fin i.n),
          And
            (@LE.le.{0} ENNReal ENNReal.instLE
              (i.dist
                (@List.take.{0} (Fin i.k)
                  (@Fin.val
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    t)
                  ds)
                v)
              (DecrAlmostLinearSSSP.Decremental.selected i b ptr v))
            (And
              (@LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.selected i b ptr v)
                (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                  (@instHMul.{0} ENNReal
                    (@Distrib.toMul.{0} ENNReal
                      (@instDistribOfSemiring.{0} ENNReal
                        (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                  (ENNReal.ofReal
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) i.accuracy))
                  (i.dist
                    (@List.take.{0} (Fin i.k)
                      (@Fin.val
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        t)
                      ds)
                    v)))
              (Iff
                (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.selected i b ptr v)
                  (@Top.top.{0} ENNReal ENNReal.instTop))
                (Not
                  (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph
                    (@DecrAlmostLinearSSSP.Decremental.live i.k
                      (@List.take.{0} (Fin i.k)
                        (@Fin.val
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@List.length.{0} (Fin i.k) ds)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          t)
                        ds))
                    i.source v))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real}
  {a : Nat → Real} {ds : List.{0} (Fin i.k)} (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds)
  (r t : Nat),
  @LE.le.{0} Nat instLENat r t →
    ∀ (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
      @LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.Native.historySup i p C a ds guides r q v)
        (@DecrAlmostLinearSSSP.Decremental.Native.historySup i p C a ds guides t q v)) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real}
  {a : Nat → Real} {ds : List.{0} (Fin i.k)} (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds)
  (t :
    Fin
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
  (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)) (v : Fin i.n),
  @LE.le.{0} ENNReal ENNReal.instLE
    (DecrAlmostLinearSSSP.Decremental.stored (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides t q)
      (@Fin.val i.n v))
    (@DecrAlmostLinearSSSP.Decremental.Native.historySup i p C a ds guides
      (@Fin.val
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        t)
      q v))))))) ∧ (((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real}
  {a : Nat → Real} {ds : List.{0} (Fin i.k)}
  (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds),
  @DecrAlmostLinearSSSP.Decremental.Native.HistoryBoundary i p C a ds guides
    (@OfNat.ofNat.{0}
      (Fin
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (nat_lit 0)
      (@Fin.instOfNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@instNeZeroNatHAdd_1 (@List.length.{0} (Fin i.k) ds)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (nat_lit 0)))
    (fun q v =>
      DecrAlmostLinearSSSP.Decremental.stored
        (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides
          (@OfNat.ofNat.{0}
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (nat_lit 0)
            (@Fin.instOfNat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@instNeZeroNatHAdd_1 (@List.length.{0} (Fin i.k) ds)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (nat_lit 0)))
          q)
        (@Fin.val i.n v))
    (DecrAlmostLinearSSSP.Decremental.Native.initialPointers i fun q v =>
      DecrAlmostLinearSSSP.Decremental.stored
        (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides
          (@OfNat.ofNat.{0}
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (nat_lit 0)
            (@Fin.instOfNat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@instNeZeroNatHAdd_1 (@List.length.{0} (Fin i.k) ds)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (nat_lit 0)))
          q)
        (@Fin.val i.n v))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real}
  {a : Nat → Real} {ds : List.{0} (Fin i.k)} (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds)
  (B : Nat) (t : Fin (@List.length.{0} (Fin i.k) ds))
  {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal} {ptr : Fin i.n → Nat},
  @DecrAlmostLinearSSSP.Decremental.Native.HistoryBoundary i p C a ds guides
      (@Fin.castSucc (@List.length.{0} (Fin i.k) ds) t) b ptr →
    have before :=
      @DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides
        (@Fin.castSucc (@List.length.{0} (Fin i.k) ds) t);
    have after :=
      @DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides (@Fin.succ (@List.length.{0} (Fin i.k) ds) t);
    have final :=
      DecrAlmostLinearSSSP.Decremental.adapterTrace i (DecrAlmostLinearSSSP.Decremental.Native.boundaryAdapter i b ptr)
        (DecrAlmostLinearSSSP.Decremental.Native.updateEventsPrefix i p B
          (@GetElem.getElem.{0, 0, 0} (List.{0} (Fin i.k)) (Fin (@List.length.{0} (Fin i.k) ds)) (Fin i.k)
            (fun xs i_1 =>
              @LT.lt.{0} Nat instLTNat (@Fin.val (@List.length.{0} (Fin i.k) ds) i_1) (@List.length.{0} (Fin i.k) xs))
            (@Fin.instGetElemFinVal.{0, 0} (List.{0} (Fin i.k)) (Fin i.k)
              (fun as i_1 => @LT.lt.{0} Nat instLTNat i_1 (@List.length.{0} (Fin i.k) as))
              (@List.length.{0} (Fin i.k) ds) (@List.instGetElemNatLtLength.{0} (Fin i.k)))
            ds t
            (@Decidable.byContradiction
              (@LT.lt.{0} Nat instLTNat (@Fin.val (@List.length.{0} (Fin i.k) ds) t) (@List.length.{0} (Fin i.k) ds))
              ((@Fin.val (@List.length.{0} (Fin i.k) ds) t).decLt (@List.length.{0} (Fin i.k) ds)) fun a =>
              (a t.isLt)))
          before after (DecrAlmostLinearSSSP.Decremental.scaleCount i));
    @DecrAlmostLinearSSSP.Decremental.Native.HistoryBoundary i p C a ds guides
      (@Fin.succ (@List.length.{0} (Fin i.k) ds) t) (@DecrAlmostLinearSSSP.Decremental.AdapterState.maxima i final)
      (@DecrAlmostLinearSSSP.Decremental.AdapterState.pointer i final))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
      @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@Nat.cast.{0} Real Real.instNatCast i.size))
          i.accuracy →
        ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real),
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
            ∀ (a : Nat → Real),
              DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
                ∀ (queryBound coefficient : Nat),
                  (∀ (x : DecrAlmostLinearSSSP.Decremental.Input),
                      x.Valid →
                        @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x.n →
                          @LE.le.{0} Nat instLENat x.W
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                x.size (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                            @LT.lt.{0} Real Real.instLT
                                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                  (@Nat.cast.{0} Real Real.instNatCast x.size))
                                x.accuracy →
                              @LT.lt.{0} Real Real.instLT x.accuracy
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                                DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false x) →
                    ∀ (ds : List.{0} (Fin i.k))
                      (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds),
                      ∃ c,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Ends
                            (DecrAlmostLinearSSSP.Decremental.Native.normalProgram coefficient p)
                            (DecrAlmostLinearSSSP.Decremental.initialMachine
                              (DecrAlmostLinearSSSP.Decremental.Native.normalProgram coefficient p) i)
                            c)
                          (And
                            (DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) coefficient
                                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                    (@instHPow.{0, 0} Nat Nat
                                      (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                    i.size (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides
                                (@OfNat.ofNat.{0}
                                  (Fin
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@List.length.{0} (Fin i.k) ds)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  (nat_lit 0)
                                  (@Fin.instOfNat
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@List.length.{0} (Fin i.k) ds)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (@instNeZeroNatHAdd_1 (@List.length.{0} (Fin i.k) ds)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                    (nat_lit 0))))
                              (fun q v =>
                                DecrAlmostLinearSSSP.Decremental.stored
                                  (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides
                                    (@OfNat.ofNat.{0}
                                      (Fin
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@List.length.{0} (Fin i.k) ds)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                      (nat_lit 0)
                                      (@Fin.instOfNat
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@List.length.{0} (Fin i.k) ds)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                        (@instNeZeroNatHAdd_1 (@List.length.{0} (Fin i.k) ds)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                        (nat_lit 0)))
                                    q)
                                  (@Fin.val i.n v))
                              (DecrAlmostLinearSSSP.Decremental.Native.initialPointers i fun q v =>
                                DecrAlmostLinearSSSP.Decremental.stored
                                  (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides
                                    (@OfNat.ofNat.{0}
                                      (Fin
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@List.length.{0} (Fin i.k) ds)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                      (nat_lit 0)
                                      (@Fin.instOfNat
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@List.length.{0} (Fin i.k) ds)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                        (@instNeZeroNatHAdd_1 (@List.length.{0} (Fin i.k) ds)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                          (@Nat.instNeZeroSucc
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                        (nat_lit 0)))
                                    q)
                                  (@Fin.val i.n v))
                              (DecrAlmostLinearSSSP.Decremental.Structured.data c))
                            (@LE.le.{0} Real Real.instLE (@Nat.cast.{0} Real Real.instNatCast c.work)
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                    (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                          (@Nat.cast.{0} Real Real.instNatCast
                                            (DecrAlmostLinearSSSP.Decremental.Native.normalInitConstant p coefficient))
                                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                              (@OfNat.ofNat.{0} Real (nat_lit 1024)
                                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 1024) Real.instNatCast
                                                  (@Nat.instAtLeastTwoHAddOfNat
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1023) (instOfNatNat (nat_lit 1023)))
                                                    (@Nat.instNeZeroSucc
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1022)
                                                        (instOfNatNat (nat_lit 1022)))))))
                                              C)))
                                        (@Nat.cast.{0} Real Real.instNatCast i.size))
                                      (DecrAlmostLinearSSSP.Decremental.normalWrapperOverhead a i.size))
                                    i.accuracy)
                                  (@Max.max.{0} Real Real.instMax
                                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                    (DecrAlmostLinearSSSP.Decremental.logarithm2
                                      (@Nat.cast.{0} Real Real.instNatCast i.W))))
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input},
  i.Valid →
    ∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real} {a : Nat → Real} {ds : List.{0} (Fin i.k)}
      {guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds}
      {t :
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
      {B reserve : Nat} {b : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i) → Fin i.n → ENNReal}
      {ptr : Fin i.n → Nat} {c : DecrAlmostLinearSSSP.Decremental.Machine},
      DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p B reserve
          (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides t) b ptr
          (DecrAlmostLinearSSSP.Decremental.Structured.data c) →
        @DecrAlmostLinearSSSP.Decremental.Native.HistoryBoundary i p C a ds guides t b ptr →
          DecrAlmostLinearSSSP.Decremental.Native.GoodBoundary i ds
            (@Fin.val
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              t)
            c) ∧ (∀ (Q delta oldWork newWork index oldEnergy newEnergy initialEnergy initialSum currentSum nextSum initialWork : Nat),
  @Eq.{1} Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) delta currentSum) nextSum →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) delta →
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) newWork
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) oldEnergy))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) oldWork
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) Q delta))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) newEnergy))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) oldWork
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) index))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) initialEnergy))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Q
                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                initialSum))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) initialWork
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Q
                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  currentSum))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) oldEnergy)) →
          @LE.le.{0} Nat instLENat
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) newWork
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) index
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) initialEnergy))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Q
                  (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                initialSum))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) initialWork
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) Q
                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                  nextSum))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) newEnergy)))))) ∧ (((∀ (a : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
    ∃ B,
      And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) B)
        (∀ (m : Nat),
          @LE.le.{0} Real Real.instLE (a m)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Nat.cast.{0} Real Real.instNatCast B)
              (@Nat.cast.{0} Real Real.instNatCast
                (@Max.max.{0} Nat Nat.instMax (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) m))))) ∧ (∀ (C : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
    ∀ (a : Nat → Real),
      DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
        ∃ B,
          And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) B)
            (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
              i.Valid →
                @LT.lt.{0} Real Real.instLT
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@Nat.cast.{0} Real Real.instNatCast i.size))
                    i.accuracy →
                  @LE.le.{0} Real Real.instLE
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 64)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 64) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62)))))))
                            (@Nat.cast.{0} Real Real.instNatCast i.size)))
                        (a
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
                      (@Inv.inv.{0} Real Real.instInv
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                          (@OfNat.ofNat.{0} Real (nat_lit 16)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                (@Nat.instNeZeroSucc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Nat.cast.{0} Real Real.instNatCast B)
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                        (@Nat.cast.{0} Real Real.instNatCast i.size)
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real}
  {a : Nat → Real} {ds : List.{0} (Fin i.k)} (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds)
  (t : Fin (@List.length.{0} (Fin i.k) ds)),
  @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (DecrAlmostLinearSSSP.Decremental.Native.updateWorkPrefix i
        (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides
          (@Fin.castSucc (@List.length.{0} (Fin i.k) ds) t))
        (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides
          (@Fin.succ (@List.length.{0} (Fin i.k) ds) t))
        (DecrAlmostLinearSSSP.Decremental.scaleCount i))
      (@DecrAlmostLinearSSSP.Decremental.Native.sourceSumWork i p C a ds guides
        (@Fin.castSucc (@List.length.{0} (Fin i.k) ds) t)))
    (@DecrAlmostLinearSSSP.Decremental.Native.sourceSumWork i p C a ds guides
      (@Fin.succ (@List.length.{0} (Fin i.k) ds) t))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real}
  {a : Nat → Real} {ds : List.{0} (Fin i.k)} (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds)
  (t :
    Fin
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
  @LE.le.{0} Real Real.instLE
    (@Nat.cast.{0} Real Real.instNatCast (@DecrAlmostLinearSSSP.Decremental.Native.sourceSumWork i p C a ds guides t))
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.scaleCount i))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 64)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 64) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62)))))))
              (@Nat.cast.{0} Real Real.instNatCast i.size)))
          (a
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          i.accuracy
          (@OfNat.ofNat.{0} Real (nat_lit 16)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real}
  {a : Nat → Real} {ds : List.{0} (Fin i.k)} (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds)
  (coefficient : Nat),
  @LE.le.{0} Real Real.instLE
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@OfNat.ofNat.{0} Real (nat_lit 64)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 64) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62)))))))
              (@Nat.cast.{0} Real Real.instNatCast i.size)))
          (a
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
        (@Inv.inv.{0} Real Real.instInv
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            i.accuracy
            (@OfNat.ofNat.{0} Real (nat_lit 16)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@Nat.cast.{0} Real Real.instNatCast coefficient)
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
          (@Nat.cast.{0} Real Real.instNatCast i.size) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) →
    ∀
      (t :
        Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (q : Fin (DecrAlmostLinearSSSP.Decremental.scaleCount i)),
      @LE.le.{0} Nat instLENat (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides t q).work
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) coefficient
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat
              (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) i.size
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) ∧ ((((∀ (C : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
    ∀ (a : Nat → Real),
      DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
        ∃ coefficient,
          And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32))) coefficient)
            (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
              i.Valid →
                @LT.lt.{0} Real Real.instLT
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@Nat.cast.{0} Real Real.instNatCast i.size))
                    i.accuracy →
                  @LE.le.{0} Real Real.instLE
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 64)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 64) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62)))))))
                            (@Nat.cast.{0} Real Real.instNatCast i.size)))
                        (a
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
                      (@Inv.inv.{0} Real Real.instInv
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                          (@OfNat.ofNat.{0} Real (nat_lit 16)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                (@Nat.instNeZeroSucc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Nat.cast.{0} Real Real.instNatCast coefficient)
                      (@HPow.hPow.{0, 0, 0} Real Nat Real
                        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                        (@Nat.cast.{0} Real Real.instNatCast i.size)
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (ds : List.{0} (Fin i.k))
      (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds) (coefficient : Nat)
      (c : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Ends (DecrAlmostLinearSSSP.Decremental.Native.normalProgram coefficient p)
          (DecrAlmostLinearSSSP.Decremental.initialMachine
            (DecrAlmostLinearSSSP.Decremental.Native.normalProgram coefficient p) i)
          c →
        DecrAlmostLinearSSSP.Decremental.Native.NormalMemory i p
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) coefficient
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) i.size
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@DecrAlmostLinearSSSP.Decremental.Native.sourceAt i p C a ds guides
              (@OfNat.ofNat.{0}
                (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (nat_lit 0)
                (@Fin.instOfNat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@instNeZeroNatHAdd_1 (@List.length.{0} (Fin i.k) ds)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                  (nat_lit 0))))
            (@DecrAlmostLinearSSSP.Decremental.Native.sourceInitialCache i p C a ds guides)
            (@DecrAlmostLinearSSSP.Decremental.Native.sourceInitialPointer i p C a ds guides)
            (DecrAlmostLinearSSSP.Decremental.Structured.data c) →
          Nonempty.{1}
            (DecrAlmostLinearSSSP.Decremental.Native.NormalRunState i p C a ds guides coefficient c
              (@OfNat.ofNat.{0}
                (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (nat_lit 0)
                (@Fin.instOfNat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@instNeZeroNatHAdd_1 (@List.length.{0} (Fin i.k) ds)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                  (nat_lit 0)))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (ds : List.{0} (Fin i.k))
      (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds) (coefficient : Nat)
      (initial : DecrAlmostLinearSSSP.Decremental.Machine) (t : Fin (@List.length.{0} (Fin i.k) ds)),
      @LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 64)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 64) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62)))))))
                  (@Nat.cast.{0} Real Real.instNatCast i.size)))
              (a
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
            (@Inv.inv.{0} Real Real.instInv
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                (@OfNat.ofNat.{0} Real (nat_lit 16)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@Nat.cast.{0} Real Real.instNatCast coefficient)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@Nat.cast.{0} Real Real.instNatCast i.size)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) →
        ∀
          (st :
            DecrAlmostLinearSSSP.Decremental.Native.NormalRunState i p C a ds guides coefficient initial
              (@Fin.castSucc (@List.length.{0} (Fin i.k) ds) t)),
          Nonempty.{1}
            (DecrAlmostLinearSSSP.Decremental.Native.NormalRunState i p C a ds guides coefficient initial
              (@Fin.succ (@List.length.{0} (Fin i.k) ds) t))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (ds : List.{0} (Fin i.k))
      (guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds) (coefficient : Nat)
      (initial : DecrAlmostLinearSSSP.Decremental.Machine),
      @LE.le.{0} Real Real.instLE
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@OfNat.ofNat.{0} Real (nat_lit 64)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 64) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62)))))))
                  (@Nat.cast.{0} Real Real.instNatCast i.size)))
              (a
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
            (@Inv.inv.{0} Real Real.instInv
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                (@OfNat.ofNat.{0} Real (nat_lit 16)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@Nat.cast.{0} Real Real.instNatCast coefficient)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@Nat.cast.{0} Real Real.instNatCast i.size)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) →
        ∀
          (st0 :
            DecrAlmostLinearSSSP.Decremental.Native.NormalRunState i p C a ds guides coefficient initial
              (@OfNat.ofNat.{0}
                (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (nat_lit 0)
                (@Fin.instOfNat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin i.k) ds)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@instNeZeroNatHAdd_1 (@List.length.{0} (Fin i.k) ds)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                  (nat_lit 0)))),
          Nonempty.{1}
            (DecrAlmostLinearSSSP.Decremental.Native.NormalRunState i p C a ds guides coefficient initial
              (Fin.last (@List.length.{0} (Fin i.k) ds)))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {C : Real}
  {a : Nat → Real} {ds : List.{0} (Fin i.k)} {guides : DecrAlmostLinearSSSP.Decremental.Native.BarrierGuides i p C a ds}
  {coefficient : Nat} {initial : DecrAlmostLinearSSSP.Decremental.Machine}
  (st :
    DecrAlmostLinearSSSP.Decremental.Native.NormalRunState i p C a ds guides coefficient initial
      (Fin.last (@List.length.{0} (Fin i.k) ds))),
  @LE.le.{0} Nat instLENat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@DecrAlmostLinearSSSP.Decremental.Native.NormalRunState.machine i p C a ds guides coefficient initial
          (Fin.last (@List.length.{0} (Fin i.k) ds)) st).work
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) (@List.length.{0} (Fin i.k) ds)))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) initial.work
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (DecrAlmostLinearSSSP.Decremental.Native.normalMaintenanceCharge p i.size)
          (@DecrAlmostLinearSSSP.Decremental.Native.sourceSumWork i p C a ds guides
            (Fin.last (@List.length.{0} (Fin i.k) ds)))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13))) i.n)
        (DecrAlmostLinearSSSP.Decremental.scaleCount i))))))) ∧ (((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (m : Nat),
  @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.Native.normalMaintenanceCharge p m)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (DecrAlmostLinearSSSP.Decremental.Native.normalUpdateConstant p)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
          (DecrAlmostLinearSSSP.Decremental.utilityDepth m))
        (@OfNat.ofNat.{0} Nat (nat_lit 32) (instOfNatNat (nat_lit 32)))))) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (coefficient : Nat) (C : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (DecrAlmostLinearSSSP.Decremental.Native.normalProgramConstant p coefficient C))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
        ∀ (a : Nat → Real),
          DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
            @LE.le.{0} Real Real.instLE
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@Nat.cast.{0} Real Real.instNatCast
                        (DecrAlmostLinearSSSP.Decremental.Native.normalMaintenanceCharge p i.size))
                      (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.scaleCount i)))
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 64)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 64) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62)))))))
                            (@Nat.cast.{0} Real Real.instNatCast i.size)))
                        (a
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                        (@OfNat.ofNat.{0} Real (nat_lit 16)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat
                              (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                              (@Nat.instNeZeroSucc
                                (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@OfNat.ofNat.{0} Real (nat_lit 13)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 13) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))))))
                    (@Nat.cast.{0} Real Real.instNatCast i.n))
                  (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.scaleCount i))))
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@Nat.cast.{0} Real Real.instNatCast
                            (DecrAlmostLinearSSSP.Decremental.Native.normalUpdateConstant p))
                          (@OfNat.ofNat.{0} Real (nat_lit 14)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 14) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))
                                (@Nat.instNeZeroSucc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))))))
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 1024)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 1024) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1023) (instOfNatNat (nat_lit 1023)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1022) (instOfNatNat (nat_lit 1022)))))))
                            C)))
                      (@Nat.cast.{0} Real Real.instNatCast i.size))
                    (DecrAlmostLinearSSSP.Decremental.normalWrapperOverhead a i.size))
                  i.accuracy)
                (@Max.max.{0} Real Real.instMax
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (DecrAlmostLinearSSSP.Decremental.logarithm2 (@Nat.cast.{0} Real Real.instNatCast i.W))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (coefficient : Nat) (C : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
        ∀ (a : Nat → Real),
          DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
            ∀ (initial work : Real),
              @LE.le.{0} Real Real.instLE initial
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@Nat.cast.{0} Real Real.instNatCast
                                (DecrAlmostLinearSSSP.Decremental.Native.normalInitConstant p coefficient))
                              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@OfNat.ofNat.{0} Real (nat_lit 1024)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 1024) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1023) (instOfNatNat (nat_lit 1023)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1022) (instOfNatNat (nat_lit 1022)))))))
                                  C)))
                            (@Nat.cast.{0} Real Real.instNatCast i.size))
                          (DecrAlmostLinearSSSP.Decremental.normalWrapperOverhead a i.size))
                        i.accuracy)
                      (@Max.max.{0} Real Real.instMax
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (DecrAlmostLinearSSSP.Decremental.logarithm2 (@Nat.cast.{0} Real Real.instNatCast i.W))))
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) →
                @LE.le.{0} Real Real.instLE work
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) initial
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@Nat.cast.{0} Real Real.instNatCast
                              (DecrAlmostLinearSSSP.Decremental.Native.normalMaintenanceCharge p i.size))
                            (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.scaleCount i)))
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@OfNat.ofNat.{0} Real (nat_lit 64)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 64) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62)))))))
                                  (@Nat.cast.{0} Real Real.instNatCast i.size)))
                              (a
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
                            (@HDiv.hDiv.{0, 0, 0} Real Real Real
                              (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                              (@OfNat.ofNat.{0} Real (nat_lit 16)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))))))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@OfNat.ofNat.{0} Real (nat_lit 13)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 13) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))))))
                          (@Nat.cast.{0} Real Real.instNatCast i.n))
                        (@Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.scaleCount i)))) →
                  @LE.le.{0} Real Real.instLE work
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (DecrAlmostLinearSSSP.Decremental.Native.normalProgramConstant p coefficient C)
                            (@Nat.cast.{0} Real Real.instNatCast i.size))
                          (DecrAlmostLinearSSSP.Decremental.normalWrapperOverhead a i.size))
                        i.accuracy)
                      (@Max.max.{0} Real Real.instMax
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (DecrAlmostLinearSSSP.Decremental.logarithm2 (@Nat.cast.{0} Real Real.instNatCast i.W))))) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real),
  @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
    ∀ (a : Nat → Real),
      DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
        ∀ (queryBound coefficient : Nat),
          (∀ (x : DecrAlmostLinearSSSP.Decremental.Input),
              x.Valid →
                @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) x.n →
                  @LE.le.{0} Nat instLENat x.W
                      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) x.size
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
                    @LT.lt.{0} Real Real.instLT
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@Nat.cast.{0} Real Real.instNatCast x.size))
                        x.accuracy →
                      @LT.lt.{0} Real Real.instLT x.accuracy
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
                        DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false x) →
            (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
                i.Valid →
                  @LT.lt.{0} Real Real.instLT
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@Nat.cast.{0} Real Real.instNatCast i.size))
                      i.accuracy →
                    @LE.le.{0} Real Real.instLE
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@OfNat.ofNat.{0} Real (nat_lit 64)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 64) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 63) (instOfNatNat (nat_lit 63)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 62) (instOfNatNat (nat_lit 62)))))))
                              (@Nat.cast.{0} Real Real.instNatCast i.size)))
                          (a
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64))) i.size)))
                        (@Inv.inv.{0} Real Real.instInv
                          (@HDiv.hDiv.{0, 0, 0} Real Real Real
                            (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid)) i.accuracy
                            (@OfNat.ofNat.{0} Real (nat_lit 16)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 16) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))))))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@Nat.cast.{0} Real Real.instNatCast coefficient)
                        (@HPow.hPow.{0, 0, 0} Real Nat Real
                          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                          (@Nat.cast.{0} Real Real.instNatCast i.size)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))) →
              ∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
                i.Valid →
                  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
                    @LT.lt.{0} Real Real.instLT
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@Nat.cast.{0} Real Real.instNatCast i.size))
                        i.accuracy →
                      DecrAlmostLinearSSSP.Decremental.Maintains
                        (DecrAlmostLinearSSSP.Decremental.Native.normalProgram coefficient p)
                        (DecrAlmostLinearSSSP.Decremental.Native.normalProgramConstant p coefficient C)
                        (DecrAlmostLinearSSSP.Decremental.normalWrapperOverhead a)
                        (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) Bool.true i))))))) := by sorry
