-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_1
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T17:33:38.772594+00:00
-- url     : https://prove2.me/theorems/da7dbcda-673e-4bc6-96df-6d8223ab18f3
-- title:
--   Normalization records and instrumented scalar executions
-- statement:
--   Let the graph, labels, caches, cut states and scalar RAM machines be the objects of the normalized decremental SSSP implementation interface. Each component below is universally quantified over its own parameters and representation hypotheses.
--
--   Finite accumulation and instrumented instruction loops terminate with the stated charged costs. Sink and permanent-edge normalization preserves the relevant original walks and separates unreachable targets by a strict distance gap. Store callbacks preserve the decoded source machine while maintaining the public readout and its address mapping. Native graph-record routines have the exact memory effects and frames stated in their component contracts.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_1 : (((((((∀ (acc counter limit factor unit : Nat),
  @Ne.{1} Nat acc counter →
    @Ne.{1} Nat acc limit →
      @Ne.{1} Nat acc factor →
        @Ne.{1} Nat acc unit →
          @Ne.{1} Nat counter limit →
            @Ne.{1} Nat counter factor →
              @Ne.{1} Nat counter unit →
                ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (q : Nat),
                  @Eq.{1} Nat (s.natReg limit)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (s.natReg counter) q) →
                    @Eq.{1} Nat (s.natReg unit) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                      ∃ t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            (DecrAlmostLinearSSSP.Decremental.Structured.accumulate acc counter limit factor unit) s
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) q)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            t)
                          (And
                            (@Eq.{1} Nat (t.natReg counter)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (s.natReg counter) q))
                            (@Eq.{1} Nat (t.natReg acc)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (s.natReg acc)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q (s.natReg factor)))))) ∧ (∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) (k : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.conditionalOne test k) s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.Structured.conditionalOneState test k s))) ∧ ((∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) (k : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Structured.conditionalOneState test k s).natMem s.natMem)
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Structured.conditionalOneState test k s).realMem s.realMem)) ∧ (∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) (k : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.Structured.conditionalOneState test k s).natReg k)
    (@ite.{1} Nat (test.holds s) (Classical.propDecidable (test.holds s))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) (s.natReg k))))) ∧ (((∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) (k j : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Ne.{1} Nat j k →
    @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.Structured.conditionalOneState test k s).natReg j) (s.natReg j)) ∧ (∀ (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) (k : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Structured.conditionalOneState test k s).realReg s.realReg)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Finset.{0} (Fin i.k)) (e : Fin i.k),
  Iff
    (@Membership.mem.{0, 0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
      (Finset.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)))
      (@SetLike.instMembership.{0, 0}
        (Finset.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)))
        (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
        (@Finset.instSetLike.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))))
      (DecrAlmostLinearSSSP.Decremental.Normalize.active i a) (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i e))
    (@Membership.mem.{0, 0} (Fin i.k) (Finset.{0} (Fin i.k))
      (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin i.k)) (Fin i.k) (@Finset.instSetLike.{0} (Fin i.k))) a e)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Finset.{0} (Fin i.k)) (v : Fin i.n),
  @Membership.mem.{0, 0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
    (Finset.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)))
    (@SetLike.instMembership.{0, 0}
      (Finset.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)))
      (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
      (@Finset.instSetLike.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))))
    (DecrAlmostLinearSSSP.Decremental.Normalize.active i a) (DecrAlmostLinearSSSP.Decremental.Normalize.addedEdge i v)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  @Function.Injective.{1, 1} (Fin i.k) (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
    (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i)))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (ds : List.{0} (Fin i.k)),
  @Eq.{1} (Finset.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)))
    (DecrAlmostLinearSSSP.Decremental.Normalize.active i (@DecrAlmostLinearSSSP.Decremental.live i.k ds))
    (@DecrAlmostLinearSSSP.Decremental.live (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)
      (@List.map.{0, 0} (Fin i.k) (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
        (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i) ds))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Finset.{0} (Fin i.k)) {u v : Fin i.n} {es : List.{0} (Fin i.k)},
  @DecrAlmostLinearSSSP.Decremental.Walk i.n i.k i.graph a u v es →
    (∀ (e : Fin i.k),
        @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k)) es e →
          @Ne.{1} (Fin i.n) (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e) i.source) →
      @DecrAlmostLinearSSSP.Decremental.Walk (DecrAlmostLinearSSSP.Decremental.Normalize.input i).n
        (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k
        (DecrAlmostLinearSSSP.Decremental.Normalize.input i).graph
        (DecrAlmostLinearSSSP.Decremental.Normalize.active i a)
        (DecrAlmostLinearSSSP.Decremental.Normalize.oldVertex i u)
        (DecrAlmostLinearSSSP.Decremental.Normalize.oldVertex i v)
        (@List.map.{0, 0} (Fin i.k) (Fin (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k)
          (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i) es))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input)
  (a : Finset.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)))
  {u v :
    Fin
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
  {es : List.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))},
  @DecrAlmostLinearSSSP.Decremental.Walk (DecrAlmostLinearSSSP.Decremental.Normalize.input i).n
      (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k (DecrAlmostLinearSSSP.Decremental.Normalize.input i).graph
      a u v es →
    @Eq.{1}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        u (DecrAlmostLinearSSSP.Decremental.Normalize.sink i) →
      @Eq.{1}
        (Fin
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        v (DecrAlmostLinearSSSP.Decremental.Normalize.sink i)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Finset.{0} (Fin i.k))
  {u w :
    Fin
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
  {es : List.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))},
  @DecrAlmostLinearSSSP.Decremental.Walk (DecrAlmostLinearSSSP.Decremental.Normalize.input i).n
      (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k (DecrAlmostLinearSSSP.Decremental.Normalize.input i).graph
      (DecrAlmostLinearSSSP.Decremental.Normalize.active i a) u w es →
    (∀ (e : Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)),
        @Membership.mem.{0, 0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
            (List.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)))
            (@List.instMembership.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)))
            es e →
          @LT.lt.{0} Nat instLTNat
            (@Fin.val (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n) e) i.k) →
      ∀ (v : Fin i.n),
        @Eq.{1}
            (Fin
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            w (DecrAlmostLinearSSSP.Decremental.Normalize.oldVertex i v) →
          ∃ x fs,
            And
              (@Eq.{1}
                (Fin
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                u (DecrAlmostLinearSSSP.Decremental.Normalize.oldVertex i x))
              (And (@DecrAlmostLinearSSSP.Decremental.Walk i.n i.k i.graph a x v fs)
                (@Eq.{1} (List.{0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))) es
                  (@List.map.{0, 0} (Fin i.k)
                    (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
                    (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i) fs)))))) ∧ (((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (a : Finset.{0} (Fin k)) (w : Fin k → Real),
  (∀ (e : Fin k),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w e)) →
    ∀ (s v : Fin n),
      @DecrAlmostLinearSSSP.Decremental.Reachable n k g a s v →
        ∃ es,
          And (@DecrAlmostLinearSSSP.Decremental.Walk n k g a s v es)
            (And (@LT.lt.{0} Nat instLTNat (@List.length.{0} (Fin k) es) n)
              (And
                (∀ (e : Fin k),
                  @Membership.mem.{0, 0} (Fin k) (List.{0} (Fin k)) (@List.instMembership.{0} (Fin k)) es e →
                    @Ne.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e) s)
                (@Eq.{1} ENNReal
                  (@DecrAlmostLinearSSSP.Decremental.distance n k g a (fun e => ENNReal.ofReal (w e)) s v)
                  (ENNReal.ofReal
                    (@List.sum.{0} Real Real.instAdd Real.instZero (@List.map.{0, 0} (Fin k) Real w es))))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (es : List.{0} (Fin i.k)),
  @Eq.{1} Real
    (@List.sum.{0} Real Real.instAdd Real.instZero
      (@List.map.{0, 0} (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n)) Real
        (fun e => @Nat.cast.{0} Real Real.instNatCast (DecrAlmostLinearSSSP.Decremental.Normalize.weight i e))
        (@List.map.{0, 0} (Fin i.k) (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
          (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i) es)))
    (@List.sum.{0} Real Real.instAdd Real.instZero
      (@List.map.{0, 0} (Fin i.k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (i.weight e)) es)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Finset.{0} (Fin i.k)) (v : Fin i.n),
  @DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph a i.source v →
    @LE.le.{0} ENNReal ENNReal.instLE
      (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.Normalize.input i).n
        (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k
        (DecrAlmostLinearSSSP.Decremental.Normalize.input i).graph
        (DecrAlmostLinearSSSP.Decremental.Normalize.active i a)
        (fun e =>
          @Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (DecrAlmostLinearSSSP.Decremental.Normalize.weight i e))
        (DecrAlmostLinearSSSP.Decremental.Normalize.source i)
        (DecrAlmostLinearSSSP.Decremental.Normalize.oldVertex i v))
      (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph a
        (fun e =>
          @Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (i.weight e))
        i.source v)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Finset.{0} (Fin i.k))
  (v :
    Fin
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
  @DecrAlmostLinearSSSP.Decremental.Reachable (DecrAlmostLinearSSSP.Decremental.Normalize.input i).n
    (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k (DecrAlmostLinearSSSP.Decremental.Normalize.input i).graph
    (DecrAlmostLinearSSSP.Decremental.Normalize.active i a) (DecrAlmostLinearSSSP.Decremental.Normalize.source i) v) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Finset.{0} (Fin i.k)) (v : Fin i.n),
  @LT.lt.{0} ENNReal (@Preorder.toLT.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
      (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.Normalize.input i).n
        (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k
        (DecrAlmostLinearSSSP.Decremental.Normalize.input i).graph
        (DecrAlmostLinearSSSP.Decremental.Normalize.active i a)
        (fun e =>
          @Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (DecrAlmostLinearSSSP.Decremental.Normalize.weight i e))
        (DecrAlmostLinearSSSP.Decremental.Normalize.source i)
        (DecrAlmostLinearSSSP.Decremental.Normalize.oldVertex i v))
      (@Nat.cast.{0} ENNReal
        (@AddMonoidWithOne.toNatCast.{0} ENNReal
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
        (DecrAlmostLinearSSSP.Decremental.Normalize.sentinel i)) →
    @LE.le.{0} ENNReal ENNReal.instLE
      (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph a
        (fun e =>
          @Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (i.weight e))
        i.source v)
      (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.Normalize.input i).n
        (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k
        (DecrAlmostLinearSSSP.Decremental.Normalize.input i).graph
        (DecrAlmostLinearSSSP.Decremental.Normalize.active i a)
        (fun e =>
          @Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (DecrAlmostLinearSSSP.Decremental.Normalize.weight i e))
        (DecrAlmostLinearSSSP.Decremental.Normalize.source i)
        (DecrAlmostLinearSSSP.Decremental.Normalize.oldVertex i v)))))))) ∧ (((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Finset.{0} (Fin i.k)),
  @Eq.{1} ENNReal
    (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph a
      (fun e =>
        @Nat.cast.{0} ENNReal
          (@AddMonoidWithOne.toNatCast.{0} ENNReal
            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
          (i.weight e))
      i.source i.source)
    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (a : Finset.{0} (Fin i.k)) (v : Fin i.n),
      @DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph a i.source v →
        @LE.le.{0} ENNReal ENNReal.instLE
          (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph a
            (fun e =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                (i.weight e))
            i.source v)
          (@Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LT.lt.{0} ENNReal (@Preorder.toLT.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
      (@Nat.cast.{0} ENNReal
        (@AddMonoidWithOne.toNatCast.{0} ENNReal
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W))
      (@Nat.cast.{0} ENNReal
        (@AddMonoidWithOne.toNatCast.{0} ENNReal
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
        (DecrAlmostLinearSSSP.Decremental.Normalize.sentinel i))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (a : Finset.{0} (Fin i.k)) (v : Fin i.n),
      @DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph a i.source v →
        @Eq.{1} ENNReal
          (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.Normalize.input i).n
            (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k
            (DecrAlmostLinearSSSP.Decremental.Normalize.input i).graph
            (DecrAlmostLinearSSSP.Decremental.Normalize.active i a)
            (fun e =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                (DecrAlmostLinearSSSP.Decremental.Normalize.weight i e))
            (DecrAlmostLinearSSSP.Decremental.Normalize.source i)
            (DecrAlmostLinearSSSP.Decremental.Normalize.oldVertex i v))
          (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph a
            (fun e =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                (i.weight e))
            i.source v)))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Finset.{0} (Fin i.k)) (v : Fin i.n),
  Not (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph a i.source v) →
    @LE.le.{0} ENNReal ENNReal.instLE
      (@Nat.cast.{0} ENNReal
        (@AddMonoidWithOne.toNatCast.{0} ENNReal
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
        (DecrAlmostLinearSSSP.Decremental.Normalize.sentinel i))
      (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.Normalize.input i).n
        (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k
        (DecrAlmostLinearSSSP.Decremental.Normalize.input i).graph
        (DecrAlmostLinearSSSP.Decremental.Normalize.active i a)
        (fun e =>
          @Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (DecrAlmostLinearSSSP.Decremental.Normalize.weight i e))
        (DecrAlmostLinearSSSP.Decremental.Normalize.source i)
        (DecrAlmostLinearSSSP.Decremental.Normalize.oldVertex i v))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (DecrAlmostLinearSSSP.Decremental.Normalize.cutoff i))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LT.lt.{0} ENNReal (@Preorder.toLT.{0} ENNReal (@PartialOrder.toPreorder.{0} ENNReal ENNReal.instPartialOrder))
      (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
        (@instHMul.{0} ENNReal
          (@Distrib.toMul.{0} ENNReal
            (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
        (ENNReal.ofReal
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) i.accuracy))
        (@Nat.cast.{0} ENNReal
          (@AddMonoidWithOne.toNatCast.{0} ENNReal
            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W)))
      (@Nat.cast.{0} ENNReal
        (@AddMonoidWithOne.toNatCast.{0} ENNReal
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
        (DecrAlmostLinearSSSP.Decremental.Normalize.cutoff i))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (a : Finset.{0} (Fin i.k)) (v : Fin i.n) (D : ENNReal),
      @LE.le.{0} ENNReal ENNReal.instLE
          (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.Normalize.input i).n
            (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k
            (DecrAlmostLinearSSSP.Decremental.Normalize.input i).graph
            (DecrAlmostLinearSSSP.Decremental.Normalize.active i a)
            (fun e =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                (DecrAlmostLinearSSSP.Decremental.Normalize.weight i e))
            (DecrAlmostLinearSSSP.Decremental.Normalize.source i)
            (DecrAlmostLinearSSSP.Decremental.Normalize.oldVertex i v))
          D →
        @LE.le.{0} ENNReal ENNReal.instLE D
            (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
              (@instHMul.{0} ENNReal
                (@Distrib.toMul.{0} ENNReal
                  (@instDistribOfSemiring.{0} ENNReal (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
              (ENNReal.ofReal
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) i.accuracy))
              (@DecrAlmostLinearSSSP.Decremental.distance (DecrAlmostLinearSSSP.Decremental.Normalize.input i).n
                (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k
                (DecrAlmostLinearSSSP.Decremental.Normalize.input i).graph
                (DecrAlmostLinearSSSP.Decremental.Normalize.active i a)
                (fun e =>
                  @Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (DecrAlmostLinearSSSP.Decremental.Normalize.weight i e))
                (DecrAlmostLinearSSSP.Decremental.Normalize.source i)
                (DecrAlmostLinearSSSP.Decremental.Normalize.oldVertex i v))) →
          And
            (@LE.le.{0} ENNReal ENNReal.instLE
              (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph a
                (fun e =>
                  @Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (i.weight e))
                i.source v)
              (DecrAlmostLinearSSSP.Decremental.Normalize.sanitize i D))
            (And
              (@LE.le.{0} ENNReal ENNReal.instLE (DecrAlmostLinearSSSP.Decremental.Normalize.sanitize i D)
                (@HMul.hMul.{0, 0, 0} ENNReal ENNReal ENNReal
                  (@instHMul.{0} ENNReal
                    (@Distrib.toMul.{0} ENNReal
                      (@instDistribOfSemiring.{0} ENNReal
                        (@CommSemiring.toSemiring.{0} ENNReal ENNReal.instCommSemiring))))
                  (ENNReal.ofReal
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) i.accuracy))
                  (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph a
                    (fun e =>
                      @Nat.cast.{0} ENNReal
                        (@AddMonoidWithOne.toNatCast.{0} ENNReal
                          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                        (i.weight e))
                    i.source v)))
              (Iff
                (@Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.Normalize.sanitize i D)
                  (@Top.top.{0} ENNReal ENNReal.instTop))
                (Not (@DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph a i.source v))))) ∧ (∀ {action : DecrAlmostLinearSSSP.Decremental.Instruction → DecrAlmostLinearSSSP.Decremental.Structured.Cmd}
  {bound : DecrAlmostLinearSSSP.Decremental.Instruction → Nat}
  {P : DecrAlmostLinearSSSP.Decremental.Structured.Data → DecrAlmostLinearSSSP.Decremental.Machine → Prop} {B F : Nat},
  DecrAlmostLinearSSSP.Decremental.Instrumented.ActionSpec action bound P B F →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (g : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F s g →
        P s g →
          ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
            ∃ cost t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  (DecrAlmostLinearSSSP.Decremental.Instrumented.instruction action g.pc ins) s cost t)
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (bound ins)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (And
                    (DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F t
                      (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                        {
                          pc :=
                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                          realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
                          halted := g.halted, fault := g.fault,
                          work :=
                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }))
                    (P t
                      (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                        {
                          pc :=
                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                          realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
                          halted := g.halted, fault := g.fault,
                          work :=
                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }))))))))) ∧ ((((∀ {action : DecrAlmostLinearSSSP.Decremental.Instruction → DecrAlmostLinearSSSP.Decremental.Structured.Cmd}
  {bound : DecrAlmostLinearSSSP.Decremental.Instruction → Nat}
  {P : DecrAlmostLinearSSSP.Decremental.Structured.Data → DecrAlmostLinearSSSP.Decremental.Machine → Prop} {B F : Nat},
  DecrAlmostLinearSSSP.Decremental.Instrumented.ActionSpec action bound P B F →
    ∀ (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (start : Nat)
      (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (g : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F s g →
        P s g →
          @LE.le.{0} Nat instLENat start g.pc →
            ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) g.pc start))
                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
                ∃ cost t,
                  And
                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                      (DecrAlmostLinearSSSP.Decremental.Instrumented.dispatch action start code) s cost t)
                    (And
                      (@LE.le.{0} Nat instLENat cost (DecrAlmostLinearSSSP.Decremental.Instrumented.charge bound code))
                      (And
                        (DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F t
                          (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                            {
                              pc :=
                                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                              realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
                              halted := g.halted, fault := g.fault,
                              work :=
                                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }))
                        (P t
                          (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                            {
                              pc :=
                                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                              realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem,
                              halted := g.halted, fault := g.fault,
                              work :=
                                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }))))) ∧ (∀ {action : DecrAlmostLinearSSSP.Decremental.Instruction → DecrAlmostLinearSSSP.Decremental.Structured.Cmd}
  {bound : DecrAlmostLinearSSSP.Decremental.Instruction → Nat}
  {P : DecrAlmostLinearSSSP.Decremental.Structured.Data → DecrAlmostLinearSSSP.Decremental.Machine → Prop} {B F : Nat},
  DecrAlmostLinearSSSP.Decremental.Instrumented.ActionSpec action bound P B F →
    ∀ (guest : DecrAlmostLinearSSSP.Decremental.Program) (t : Nat)
      (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (g : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F s g →
        P s g →
          (∀ (j : Nat),
              @LT.lt.{0} Nat instLTNat j t →
                @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute guest g j).halted Bool.false →
                  ∃ ins,
                    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                        DecrAlmostLinearSSSP.Decremental.Instruction
                        (fun as i =>
                          @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) guest.code
                        (DecrAlmostLinearSSSP.Decremental.execute guest g j).pc)
                      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins)) →
            @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute guest g t).halted Bool.true →
              ∃ cost u,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    (DecrAlmostLinearSSSP.Decremental.Instrumented.interpreter action guest.code) s cost u)
                  (And
                    (@LE.le.{0} Nat instLENat cost
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (DecrAlmostLinearSSSP.Decremental.Instrumented.charge bound guest.code)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          t)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (And
                      (DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F u
                        (DecrAlmostLinearSSSP.Decremental.execute guest g t))
                      (P u (DecrAlmostLinearSSSP.Decremental.execute guest g t)))))) ∧ ((∀ {action : DecrAlmostLinearSSSP.Decremental.Instruction → DecrAlmostLinearSSSP.Decremental.Structured.Cmd}
  {bound : DecrAlmostLinearSSSP.Decremental.Instruction → Nat}
  {P : DecrAlmostLinearSSSP.Decremental.Structured.Data → DecrAlmostLinearSSSP.Decremental.Machine → Prop} {B F : Nat},
  DecrAlmostLinearSSSP.Decremental.Instrumented.ActionSpec action bound P B F →
    ∀ (guest : DecrAlmostLinearSSSP.Decremental.Program) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
      (g final : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F s g →
        P s g →
          DecrAlmostLinearSSSP.Decremental.Ends guest g final →
            ∃ cost u,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  (DecrAlmostLinearSSSP.Decremental.Instrumented.interpreter action guest.code) s cost u)
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (DecrAlmostLinearSSSP.Decremental.Instrumented.charge bound guest.code)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) final.work g.work))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (And (DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F u final) (P u final)))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.inner s
    (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.committed s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.prepared s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
        (s.natMem
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.prepared s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
          (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.prepared s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (And
            (@Eq.{1} Real
              ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.prepared s).realReg
                (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))
              (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
            (And
              (@Eq.{1} Real
                ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.prepared s).realReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))))
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.prepared s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.flagged s).natReg
      (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
    (@ite.{1} Nat
      (Or
        (@LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))
        (@LT.lt.{0} Real Real.instLT (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))))
      (@instDecidableOr
        (@LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))
        (@LT.lt.{0} Real Real.instLT (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))))
        ((s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).decLt
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))
        ((s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))).decidableLT
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    And
      (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.committed s).natMem
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
          (s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@ite.{1} Nat
            (Or
              (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
              (@LT.lt.{0} Real Real.instLT (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
            (@instDecidableOr
              (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
              (@LT.lt.{0} Real Real.instLT (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
              (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))
              ((s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))).decidableLT
                (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
      (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.committed s).realMem
        (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
          (s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (s.realMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))))))) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.Normalize.Native.callback k) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.callback k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.inner k))))))) ∧ ((((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.inner k) ∧ (∀ {B : Nat} (n : Nat),
  @LE.le.{0} Nat instLENat n B →
    ∀ {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
      DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) s
          g →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @LT.lt.{0} Nat instLTNat
              (s.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              n →
            DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (DecrAlmostLinearSSSP.Decremental.Normalize.Native.committed s) g)) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {bad : Option.{0} Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B bad s g →
    DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B bad
      { realReg := s.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))),
        realMem := s.realMem, natMem := s.natMem }
      {
        pc :=
          @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.pc
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
        realReg := g.realReg, natReg := g.natReg, realMem := g.realMem, natMem := g.natMem, halted := g.halted,
        fault := g.fault,
        work :=
          @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {bad : Option.{0} Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B bad s g →
    ∀ (x : Nat),
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B bad
        { realReg := s.realReg,
          natReg :=
            @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) x,
          realMem := s.realMem, natMem := s.natMem }
        g))) ∧ (((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {bad : Option.{0} Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B bad s g →
    (∀ (v : Fin i.n), @Ne.{1} (Option.{0} Nat) bad (@Option.some.{0} Nat (@Fin.val i.n v))) →
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat) s g) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat) s g →
    (∀ (v : Fin i.n),
        And
          (@LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n v))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq.{1} Nat (g.natMem (@Fin.val i.n v)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (g.realMem (@Fin.val i.n v)))) →
      ∀ (v : Fin i.n),
        And
          (@LE.le.{0} Nat instLENat (s.natMem (@Fin.val i.n v))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq.{1} Nat (s.natMem (@Fin.val i.n v)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (s.realMem (@Fin.val i.n v))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat) s g →
    ∀ (v : Fin i.n),
      @LE.le.{0} Nat instLENat (g.natMem (@Fin.val i.n v))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val i.n v))
          (DecrAlmostLinearSSSP.Decremental.Normalize.sanitize i
            (DecrAlmostLinearSSSP.Decremental.stored g (@Fin.val i.n v)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    ∃ t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode s
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
          t)
        (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))
          (DecrAlmostLinearSSSP.Decremental.Normalize.sentinel i))) ∧ (∀ (entry : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerCode entry)
    s (@OfNat.ofNat.{0} Nat (nat_lit 24) (instOfNatNat (nat_lit 24)))
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerData entry s)))))) ∧ ((((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 76) (instOfNatNat (nat_lit 76))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode k)) ∧ ((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode k) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode s cost
        t →
      DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i t) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.weightCode s cost
        t →
      @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 76) (instOfNatNat (nat_lit 76))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) ∧ (((∀ (entry : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NoMemory
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerCode entry)) ∧ (∀ (entry k : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) k →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerCode entry) k)) ∧ ((∀ (entry k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 28) (instOfNatNat (nat_lit 28))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
            (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerCode entry) k) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s).natMem
      (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))))))
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s).realMem s.realMem))))))) ∧ (((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88))))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldCode
          k)) ∧ ((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldCode k) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  ∃ cost,
    And
      (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.headRedirect s
        cost (DecrAlmostLinearSSSP.Decremental.Normalize.Native.redirected s))
      (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  ∃ cost,
    And
      (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.headCode s
        cost (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s))
      (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    And
      (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s).natMem
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
            (@ite.{1} Nat
              (@Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
              (instDecidableEqNat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66))))
              (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))))))))
      (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s).realMem s.realMem))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88))))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.headCode
          k) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.headCode k))))) ∧ ((((∀ {B bank logical value : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {natural : Nat → Nat}
  {real : Nat → Real},
  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank s natural real →
    @Eq.{1} (Nat → Nat) t.natMem
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
          (DecrAlmostLinearSSSP.Decremental.bankAddress B bank logical)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (DecrAlmostLinearSSSP.Decremental.bankFactor bank) value)) →
      @Eq.{1} (Nat → Real) t.realMem s.realMem →
        DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B bank t
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat natural logical value) real) ∧ (∀ (B logical : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (natural : Nat → Nat) (real : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) s
      natural real →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
        (DecrAlmostLinearSSSP.Decremental.bankAddress B (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          logical) →
      DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s)
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat natural logical
          (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))))
        real)) ∧ ((∀ (B logical : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (natural : Nat → Nat) (real : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) s
      natural real →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
        (DecrAlmostLinearSSSP.Decremental.bankAddress B (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          logical) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s)
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat natural logical
            (@ite.{1} Nat
              (@Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
              (instDecidableEqNat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66))))
              (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))))))
          real) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (B : Nat),
  @LE.le.{0} Nat instLENat B (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82)))) →
    ∀ (a : Nat),
      @LT.lt.{0} Nat instLTNat a B →
        And (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s).natMem a) (s.natMem a))
          (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s).realMem a) (s.realMem a))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (B : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @LE.le.{0} Nat instLENat B (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82)))) →
      ∀ (a : Nat),
        @LT.lt.{0} Nat instLTNat a B →
          And (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s).natMem a) (s.natMem a))
            (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s).realMem a) (s.realMem a)))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  ∃ cost,
    And
      (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordCode s
        cost (DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s))
      (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 21) (instOfNatNat (nat_lit 21))))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordCode k)) ∧ ((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordCode k) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88))))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
              (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i
      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s))))))))) := by sorry
