-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_3
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:13:28.034642+00:00
-- url     : https://prove2.me/theorems/b548e93e-828b-47a9-a7df-882dab4b4a54
-- title:
--   Native radix-trie insertion and extraction contracts
-- statement:
--   This collection gives the universally quantified contracts for native radix-trie insertion and extraction contracts. All graph identifiers, queue keys, payloads, registers and addresses are finite natural indices; capacities and arithmetic registers use the scalar RAM types defined in the accompanying interface.
--
--   For a separated radix-trie memory image, native insertion and minimum extraction realize the corresponding mathematical queue operations. The contracts specify branch descent, node creation, payload-list writes, ancestor counts, preservation of unrelated memory, and register frames. Insertion costs at most $43(h+1)$ instructions and extraction at most $34(h+1)$ instructions when the trie height is $h$. The collection includes the intermediate frame and representation facts used to compose these operations.
--
--   Each listed contract holds for every state and parameter tuple satisfying its explicit representation and domain hypotheses. Together they assert
--
--   $$
--   \bigwedge_{j\in J} L_j,
--   $$
--
--   where $L_j$ are the component queue, execution, representation, frame and work contracts described above. The conjunction preserves their individual quantifiers; it adds no successful-execution or correctness assumption to the external graph input.
--
--   These contracts form a reusable verification interface for the charged exact-recomputation branch of the general-domain reduction. **Formalization Note** The conjunction is balanced to expose component contracts through short projections and keep verification jobs within the service's compilation limit.
-- source:
--   Cui, Li, Miao and Wang, Partially Dynamic Single-Source Shortest Paths in Almost-Linear Time, October 2026 submission #912, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/912.pdf, p.4 unnumbered exact-recomputation reduction and p.18 scalar unit-cost arithmetic model. Component contracts verify the concrete native compiler, radix-trie queue, graph representation and Dijkstra implementation in DecrAlmostLinearSSSP_RAMFoundation.

import Definitions.Def_DecrAlmostLinearSSSP_RAMFoundation
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable

theorem DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_3 : (((((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 272) (instOfNatNat (nat_lit 272))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 274) (instOfNatNat (nat_lit 274))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Allocate.item k) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Allocate.item k)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
        ∃ cost t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.ensureNode
              s cost t)
            (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
              (And
                (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
                  (@ite.{1} Nat
                    (@Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (instDecidableEqNat
                      (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                    (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))))
                (And
                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                    (@ite.{1} Nat
                      (@Eq.{1} Nat
                        (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (instDecidableEqNat
                        (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))))
                  (And
                    (@Eq.{1} Nat (t.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                      (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))))
                    (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                      (And
                        (@Eq.{1} Nat
                            (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                          DecrAlmostLinearSSSP.Decremental.Exact.Allocate.NodeImage t
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                            { count := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
                              left := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
                              right := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
                              payload := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)) })
                        (∀ (address : Nat),
                          @Ne.{1} Nat address
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))) →
                            Or
                                (@LT.lt.{0} Nat instLTNat address
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                                (@LE.le.{0} Nat instLENat
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                  address) →
                              @Eq.{1} Nat (t.natMem address) (s.natMem address))))))))) ∧ (∀ (height fresh : Nat),
  @Eq.{1} Nat
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.empty height) fresh))
    fresh))) ∧ (((∀ {height : Nat} (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height) (fresh : Nat),
  @Ne.{1} (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height) tree
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.empty height) →
    @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height)
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height tree fresh) tree) ∧ (∀ {height : Nat} (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height) (fresh key value : Nat),
  @Eq.{1} (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)
    (DecrAlmostLinearSSSP.Decremental.RadixQueue.insert height key value
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract height
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height tree fresh)))
    (DecrAlmostLinearSSSP.Decremental.RadixQueue.insert height key value
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract height tree)))) ∧ ((∀ {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} (height fresh : Nat),
  DecrAlmostLinearSSSP.Decremental.Exact.Allocate.NodeImage s fresh
      { count := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
        left := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
        right := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
        payload := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)) } →
    @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s height
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.empty height) fresh)) ∧ ((∀ (height fresh : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fresh →
    @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated height
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.empty height) fresh)) ∧ (∀ (height fresh : Nat),
  @Eq.{1} (Finset.{0} Nat)
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint height
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.empty height) fresh))
    (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder fresh
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) fresh
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))))) ∧ ((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Ne.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.ensureNode s
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.loaded s)) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 272) (instOfNatNat (nat_lit 272))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 274) (instOfNatNat (nat_lit 274))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.Exact.TriePush.ensureNode k)) ∧ ((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePush.ensureNode k) ∧ (∀ {height : Nat} (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height) (low : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s height tree →
        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated height tree →
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded height tree low
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
            @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree) →
              @LE.le.{0} Nat instLENat low
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))) →
                @LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))))
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
                  ∃ cost t,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                        DecrAlmostLinearSSSP.Decremental.Exact.TriePush.ensureNode s cost t)
                      (And
                        (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                        (And
                          (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
                            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height
                              (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height tree
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))))
                          (And
                            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                              (@ite.{1} Nat
                                (@Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                (instDecidableEqNat
                                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))))
                            (And
                              (@Eq.{1} Nat
                                (t.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height
                                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height tree
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))))
                              (And
                                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image t height
                                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height tree
                                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))))
                                (And
                                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated height
                                    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height tree
                                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))))
                                  (And
                                    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded height
                                      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height tree
                                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                                      low (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                                    (And
                                      (@LE.le.{0} (Finset.{0} Nat)
                                        (@Preorder.toLE.{0} (Finset.{0} Nat)
                                          (@PartialOrder.toPreorder.{0} (Finset.{0} Nat)
                                            (@Finset.instPartialOrder.{0} Nat)))
                                        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint height
                                          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize height tree
                                            (s.natReg
                                              (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))))
                                        (@Union.union.{0} (Finset.{0} Nat)
                                          (@Finset.instUnion.{0} Nat instDecidableEqNat)
                                          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint height tree)
                                          (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                                            (t.natReg
                                              (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))))
                                      (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                                        (∀ (address : Nat),
                                          @Ne.{1} Nat address
                                              (s.natReg
                                                (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))) →
                                            Or
                                                (@LT.lt.{0} Nat instLTNat address
                                                  (s.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                                                (@LE.le.{0} Nat instLENat
                                                  (t.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                                                  address) →
                                              @Eq.{1} Nat (t.natMem address) (s.natMem address)))))))))))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.increment s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.incremented s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    And
      (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.incremented s).natMem
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.incremented s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 266) (instOfNatNat (nat_lit 266))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafPrepare s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafPrepared s)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafPrepared s).natReg
        (@OfNat.ofNat.{0} Nat (nat_lit 280) (instOfNatNat (nat_lit 280))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafPrepared s).natReg
        (@OfNat.ofNat.{0} Nat (nat_lit 276) (instOfNatNat (nat_lit 276))))
      (s.natMem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.start s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.started s))))))) ∧ (((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.started s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 236) (instOfNatNat (nat_lit 236)))))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.started s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 238) (instOfNatNat (nat_lit 238)))))
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.started s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinish s
    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinished s))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (address count head : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))) address →
        @Eq.{1} Nat (s.natMem address) count →
          @Eq.{1} Nat
              (s.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
              head →
            And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinished s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (And
                (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinished s).natMem
                  (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                    (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                      (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem address
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) count
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262)))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      head)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))))
                (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinished s).realMem
                  s.realMem))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 266) (instOfNatNat (nat_lit 266))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 282) (instOfNatNat (nat_lit 282))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 280) (instOfNatNat (nat_lit 280))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 276) (instOfNatNat (nat_lit 276))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 272) (instOfNatNat (nat_lit 272))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 274) (instOfNatNat (nat_lit 274))) →
              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))) →
                DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                  DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinish k))) ∧ (((∀ (address : Nat) (items : List.{0} (Prod.{0, 0} Nat Nat)) (low : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))) address →
        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address items) →
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address items) →
            @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address items) low
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
              have next :=
                DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address
                  (@List.cons.{0} (Prod.{0, 0} Nat Nat)
                    (@Prod.mk.{0, 0} Nat Nat
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262)))))
                    items);
              And
                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image
                  (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinished s)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next)
                (And
                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next)
                  (And
                    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next low
                      ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinished s).natReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                    (And
                      (@Eq.{1}
                        (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next)
                        (DecrAlmostLinearSSSP.Decremental.RadixQueue.insert
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))))
                          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                            (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address items))))
                      (And
                        (@LE.le.{0} (Finset.{0} Nat)
                          (@Preorder.toLE.{0} (Finset.{0} Nat)
                            (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
                          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next)
                          (@Union.union.{0} (Finset.{0} Nat) (@Finset.instUnion.{0} Nat instDecidableEqNat)
                            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                              (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address items))
                            (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                              ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinished s).natReg
                                (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))))
                        (∀
                          a ∉
                            @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                              (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address items),
                          Or
                              (@LT.lt.{0} Nat instLTNat a
                                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                              (@LE.le.{0} Nat instLENat
                                ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinished s).natReg
                                  (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                                a) →
                            @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.leafFinished s).natMem a)
                              (s.natMem a))))))) ∧ (∀
  (tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (low : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree →
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree →
            @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree low
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
              @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree) →
                @LE.le.{0} Nat instLENat low
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))) →
                  @LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))))
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
                    s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))) ∉
                        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree →
                      ∃ cost t next,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))))
                            (And
                              (@Eq.{1} Nat
                                (t.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next))
                              (And
                                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image t
                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next)
                                (And
                                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
                                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next)
                                  (And
                                    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next low
                                      (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                                    (And
                                      (@Eq.{1}
                                        (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next)
                                        (DecrAlmostLinearSSSP.Decremental.RadixQueue.insert
                                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))))
                                          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract
                                            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree)))
                                      (And
                                        (@LE.le.{0} Nat instLENat
                                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                                          (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                                        (And
                                          (@LE.le.{0} (Finset.{0} Nat)
                                            (@Preorder.toLE.{0} (Finset.{0} Nat)
                                              (@PartialOrder.toPreorder.{0} (Finset.{0} Nat)
                                                (@Finset.instPartialOrder.{0} Nat)))
                                            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                                              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) next)
                                            (@Union.union.{0} (Finset.{0} Nat)
                                              (@Finset.instUnion.{0} Nat instDecidableEqNat)
                                              (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                                                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree)
                                              (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                                                (s.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                                                (t.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))))
                                          (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                                            (∀ (address : Nat),
                                              @Ne.{1} Nat address
                                                  (s.natReg
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))) →
                                                address ∉
                                                    @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                                      tree →
                                                  Or
                                                      (@LT.lt.{0} Nat instLTNat address
                                                        (s.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 244)
                                                            (instOfNatNat (nat_lit 244)))))
                                                      (@LE.le.{0} Nat instLENat
                                                        (t.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 244)
                                                            (instOfNatNat (nat_lit 244))))
                                                        address) →
                                                    @Eq.{1} Nat (t.natMem address) (s.natMem address))))))))))))) ∧ ((∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {a b : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s a t →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s b u →
      And (@Eq.{1} Nat a b) (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data t u)) ∧ ((∀ (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.NoStore a.instruction →
    And (@Eq.{1} (Nat → Real) (a.effect s).realMem s.realMem) (@Eq.{1} (Nat → Nat) (a.effect s).natMem s.natMem)) ∧ (∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.NoMemory cmd →
      And (@Eq.{1} (Nat → Real) t.realMem s.realMem) (@Eq.{1} (Nat → Nat) t.natMem s.natMem)))))) ∧ ((((∀ (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.NoRealStore a.instruction →
    @Eq.{1} (Nat → Real) (a.effect s).realMem s.realMem) ∧ (∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.NoRealMemory cmd → @Eq.{1} (Nat → Real) t.realMem s.realMem)) ∧ ((∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePush.registers,
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core k) ∧ ((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core k) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.NoRealMemory DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core)))) ∧ (((∀ {s u t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {c d : Nat},
  (DecrAlmostLinearSSSP.Decremental.Structured.Test.natLess
          (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
          (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256)))).holds
      s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.body s c u →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core u d t →
        DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.core s
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c d)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          t) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descend s
    (@ite.{1} Nat
      (@LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
        (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))))
      ((s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))).decLt
        (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))))
      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descended s))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (h : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descended s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))))
          h)
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descended s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descended s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
                (@ite.{1} Nat
                  (@LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                    (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))))
                  ((s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))).decLt
                    (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descended s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                (@ite.{1} Nat
                  (@LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                    (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))))
                  ((s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))).decLt
                    (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                    (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))))))
              (And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descended s).natMem s.natMem)
                (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descended s).realMem
                  s.realMem)))))) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 268) (instOfNatNat (nat_lit 268))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 282) (instOfNatNat (nat_lit 282))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descend k) ∧ (∀ {h : Nat} (b : Bool) (a : Nat) (c o : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h),
  @Eq.{1} Nat
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b a c o))
    a))))))) ∧ ((((((∀ {h : Nat} (b : Bool) (a : Nat) (c o : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h),
  @Eq.{1} (Finset.{0} Nat)
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b a c o))
    (@Union.union.{0} (Finset.{0} Nat) (@Finset.instUnion.{0} Nat instDecidableEqNat)
      (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder a
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
      (@Union.union.{0} (Finset.{0} Nat) (@Finset.instUnion.{0} Nat instDecidableEqNat)
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h c)
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h o)))) ∧ (∀ {h : Nat} (b : Bool) (a : Nat) (c o : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  Iff
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b a c o))
    (And
      (@Eq.{1} Nat (s.natMem a)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h c))
          (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h o))))
      (And
        (@Eq.{1} Nat
          (s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
              (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.childOffset b)))
          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h c))
        (And
          (@Eq.{1} Nat
            (s.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
                (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.otherOffset b)))
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h o))
          (And (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s h c)
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s h o))))))) ∧ ((∀ {h : Nat} (b : Bool) (a : Nat) (c o : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h),
  Iff
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b a c o))
    (And (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) a)
      (And
        (@Disjoint.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat) (@Finset.instOrderBot.{0} Nat)
          (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder a
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
          (@Union.union.{0} (Finset.{0} Nat) (@Finset.instUnion.{0} Nat instDecidableEqNat)
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h c)
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h o)))
        (And
          (@Disjoint.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat) (@Finset.instOrderBot.{0} Nat)
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h c)
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h o))
          (And (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated h c)
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated h o)))))) ∧ (∀ {h : Nat} (b : Bool) (a : Nat) (c o : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h) (r : Nat),
  @LT.lt.{0} Nat instLTNat r (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b a c o))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a r)))) ∧ (((∀ {h : Nat} (b : Bool) (a : Nat) (c o : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h),
  @LE.le.{0} (Finset.{0} Nat)
    (@Preorder.toLE.{0} (Finset.{0} Nat)
      (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h c)
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b a c o))) ∧ (∀ {h : Nat} (b : Bool) (a : Nat) (c o : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h),
  @LE.le.{0} (Finset.{0} Nat)
    (@Preorder.toLE.{0} (Finset.{0} Nat)
      (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h o)
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b a c o)))) ∧ ((∀ (b : Bool),
  And
    (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.childOffset b))
    (@LT.lt.{0} Nat instLTNat (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.childOffset b)
      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))) ∧ ((∀ (b : Bool),
  @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.otherOffset b)
    (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.childOffset b)) ∧ (∀ (b : Bool),
  @LT.lt.{0} Nat instLTNat (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.otherOffset b)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))) ∧ ((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 266) (instOfNatNat (nat_lit 266))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePush.increment k) ∧ (∀ (h address power : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))) address →
        @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))) power →
          @Ne.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258)))) address →
            have t :=
              DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descended
                (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.incremented s);
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.increment.seq
                  DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descend)
                s
                (@ite.{1} Nat
                  (@LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                    power)
                  ((s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))).decLt power)
                  (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
                t)
              (And (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256)))) h)
                (And
                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (And
                    (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address
                        (@ite.{1} Nat
                          (@LT.lt.{0} Nat instLTNat
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))) power)
                          ((s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))).decLt power)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                    (And
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                        (@ite.{1} Nat
                          (@LT.lt.{0} Nat instLTNat
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))) power)
                          ((s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))).decLt power)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))) power)))
                      (And
                        (@Eq.{1} (Nat → Nat) t.natMem
                          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem address
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (s.natMem address)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                          (∀ (k : Nat),
                            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 266) (instOfNatNat (nat_lit 266))) →
                              @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 268) (instOfNatNat (nat_lit 268))) →
                                @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 282) (instOfNatNat (nat_lit 282))) →
                                  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))) →
                                    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))) →
                                      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))) →
                                        @Ne.{1} Nat k
                                            (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))) →
                                          @Eq.{1} Nat (t.natReg k) (s.natReg k)))))))))) ∧ ((∀ {h : Nat} (b : Bool) (address : Nat) (child other next : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h)
  (low fresh stop : Nat) (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address child other) →
    @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address child other) →
      @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address child other) low fresh →
        @LE.le.{0} Nat instLENat fresh stop →
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image t h next →
            @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated h next →
              @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded h next low stop →
                @LE.le.{0} (Finset.{0} Nat)
                    (@Preorder.toLE.{0} (Finset.{0} Nat)
                      (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
                    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h next)
                    (@Union.union.{0} (Finset.{0} Nat) (@Finset.instUnion.{0} Nat instDecidableEqNat)
                      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h child)
                      (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder fresh stop)) →
                  @Eq.{1} Nat
                      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
                        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h next))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
                          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h child))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
                    @Eq.{1} Nat
                        (t.natMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address
                            (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.childOffset b)))
                        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h next) →
                      (∀ (a : Nat),
                          @Ne.{1} Nat a
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address
                                (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.childOffset b)) →
                            a ∉ @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h child →
                              Or (@LT.lt.{0} Nat instLTNat a fresh) (@LE.le.{0} Nat instLENat stop a) →
                                @Eq.{1} Nat (t.natMem a)
                                  (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem address
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (s.natMem address)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    a)) →
                        And
                          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image t
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address next other))
                          (And
                            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address next other))
                            (And
                              (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address next other) low
                                stop)
                              (@LE.le.{0} (Finset.{0} Nat)
                                (@Preorder.toLE.{0} (Finset.{0} Nat)
                                  (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
                                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address next other))
                                (@Union.union.{0} (Finset.{0} Nat) (@Finset.instUnion.{0} Nat instDecidableEqNat)
                                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address child
                                      other))
                                  (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder fresh stop)))))) ∧ ((∀ {h : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h} {low : Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (r : @DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result h tree low s),
  ∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePush.registers,
    @Eq.{1} Nat ((@DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result.final h tree low s r).natReg k) (s.natReg k)) ∧ (∀
  (tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (low : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree →
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree →
            @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree low
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
              @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))))
                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree) →
                @LE.le.{0} Nat instLENat low
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))) →
                  @LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))))
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
                    s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278))) ∉
                        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree →
                      Nonempty.{1}
                        (@DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree low s))))) ∧ (((∀
  (tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
  (low base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Ready (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      tree low base s →
    Nonempty.{1}
      (@DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) tree low s)) ∧ (∀ {h : Nat} (b : Bool) (address : Nat) (child other : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h)
  (low base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Ready
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.branch h b address child other) low base s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))) address →
      @Eq.{1} Bool b
          (@ite.{1} Bool
            (@LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h))
            ((s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))).decLt
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h))
            Bool.false Bool.true) →
        @DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Ready h child low base
          (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.descended
            (DecrAlmostLinearSSSP.Decremental.Exact.TriePush.incremented s)))) ∧ ((∀ {h : Nat} (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h) (low base : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Ready h tree low base s →
    ∃ cost u,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.ensureNode s
          cost u)
        (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
          (And
            (@Eq.{1} Nat (u.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
              (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h
                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize h tree
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))))
            (And
              (@DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Ready h
                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize h tree
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                low base u)
              (And
                (@LE.le.{0} Nat instLENat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                  (u.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                (And
                  (@LE.le.{0} (Finset.{0} Nat)
                    (@Preorder.toLE.{0} (Finset.{0} Nat)
                      (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
                    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h
                      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.materialize h tree
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))))
                    (@Union.union.{0} (Finset.{0} Nat) (@Finset.instUnion.{0} Nat instDecidableEqNat)
                      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h tree)
                      (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                        (u.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))))
                  (And (@Eq.{1} (Nat → Real) u.realMem s.realMem)
                    (∀ (a : Nat),
                      @Ne.{1} Nat a (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))) →
                        Or
                            (@LT.lt.{0} Nat instLTNat a
                              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                            (@LE.le.{0} Nat instLENat
                              (u.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) a) →
                          @Eq.{1} Nat (u.natMem a) (s.natMem a))))))))) ∧ ((∀ (h : Nat),
  (∀ (child : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h) (low base : Nat)
      (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      @DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Ready h child low base s →
        Nonempty.{1} (@DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result h child low s)) →
    ∀
      (tree :
        DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (low base : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      @DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Ready
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          tree low base s →
        Nonempty.{1}
          (@DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            tree low s)) ∧ (∀ (h : Nat) (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h) (low base : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Ready h tree low base s →
    Nonempty.{1} (@DecrAlmostLinearSSSP.Decremental.Exact.TriePush.Result h tree low s))))))) ∧ (((((∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePush.registers,
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code k) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code k)) ∧ ((∀ (h : Nat) (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h) (low base : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 236) (instOfNatNat (nat_lit 236)))) h →
        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s h tree →
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated h tree →
            @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded h tree low
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
              @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246)))))
                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h tree) →
                @LE.le.{0} Nat instLENat low
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246)))) →
                  @LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246))))
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))) →
                    s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246))) ∉
                        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h tree →
                      (∀ (j : Nat),
                          @LT.lt.{0} Nat instLTNat j h →
                            @Eq.{1} Nat
                              (s.natMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base j))
                              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) j)) →
                        @LE.le.{0} Nat instLENat
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base h) low →
                          (@Ne.{1} Nat h (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                              @Eq.{1} Nat
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 238) (instOfNatNat (nat_lit 238))))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base h)) →
                            ∃ cost t next,
                              And
                                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                  DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code s cost t)
                                (And
                                  (@LE.le.{0} Nat instLENat cost
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 43) (instOfNatNat (nat_lit 43)))
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                  (And
                                    (@Eq.{1} Nat
                                      (t.natMem
                                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246)))))
                                      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root h next))
                                    (And (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image t h next)
                                      (And (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated h next)
                                        (And
                                          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded h next low
                                            (t.natReg
                                              (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                                          (And
                                            (@Eq.{1} (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h)
                                              (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h next)
                                              (DecrAlmostLinearSSSP.Decremental.RadixQueue.insert h
                                                (s.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                                                (s.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))))
                                                (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h tree)))
                                            (And
                                              (@LE.le.{0} Nat instLENat
                                                (s.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                                                (t.natReg
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                                              (And
                                                (@LE.le.{0} (Finset.{0} Nat)
                                                  (@Preorder.toLE.{0} (Finset.{0} Nat)
                                                    (@PartialOrder.toPreorder.{0} (Finset.{0} Nat)
                                                      (@Finset.instPartialOrder.{0} Nat)))
                                                  (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h next)
                                                  (@Union.union.{0} (Finset.{0} Nat)
                                                    (@Finset.instUnion.{0} Nat instDecidableEqNat)
                                                    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h
                                                      tree)
                                                    (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder
                                                      (s.natReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 244)
                                                          (instOfNatNat (nat_lit 244))))
                                                      (t.natReg
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 244)
                                                          (instOfNatNat (nat_lit 244)))))))
                                                (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                                                  (∀ (address : Nat),
                                                    @Ne.{1} Nat address
                                                        (s.natReg
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 246)
                                                            (instOfNatNat (nat_lit 246)))) →
                                                      address ∉
                                                          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
                                                            h tree →
                                                        Or
                                                            (@LT.lt.{0} Nat instLTNat address
                                                              (s.natReg
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 244)
                                                                  (instOfNatNat (nat_lit 244)))))
                                                            (@LE.le.{0} Nat instLENat
                                                              (t.natReg
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 244)
                                                                  (instOfNatNat (nat_lit 244))))
                                                              address) →
                                                          @Eq.{1} Nat (t.natMem address) (s.natMem address)))))))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.decrement s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.decremented s)))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.decremented s).natMem
      (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
        (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
          (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leftPointer s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leftPointerData s))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leafFinish s
    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leafFinished s)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leaf s
    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leafData s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.start s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.started s)))))) ∧ ((((∀ k ∉ DecrAlmostLinearSSSP.Decremental.Exact.TriePop.registers,
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePop.core k) ∧ (∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePop.core k)) ∧ ((DecrAlmostLinearSSSP.Decremental.Structured.NoRealMemory DecrAlmostLinearSSSP.Decremental.Exact.TriePop.core) ∧ ((∀ {s u t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {c d : Nat},
  (DecrAlmostLinearSSSP.Decremental.Structured.Test.natLess
          (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
          (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256)))).holds
      s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.body s c u →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.core u d t →
        DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.core s
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c d)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          t) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ c,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leftCount s c
          (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leftCountData s))
        (@LE.le.{0} Nat instLENat c (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ c,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.choose s c
          (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.chosen s))
        (@LE.le.{0} Nat instLENat c (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ c,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descend s c
          (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descended s))
        (@LE.le.{0} Nat instLENat c (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (h : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
        have left :=
          s.natMem
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))));
        have count :=
          @ite.{1} Nat (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) left)
            (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) left) (s.natMem left)
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)));
        And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descended s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
            (@ite.{1} Nat (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) count)
              (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) count) left
              (s.natMem
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descended s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                (@ite.{1} Nat
                  (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) count)
                  (Nat.decLt (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) count)
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                  (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descended s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))))
                h)
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descended s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descended s).natMem s.natMem)
                  (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descended s).realMem
                    s.realMem)))))) ∧ ((∀
  k ∉
    @Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256)))
      (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 258) (instOfNatNat (nat_lit 258)))
        (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))
          (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))
            (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 268) (instOfNatNat (nat_lit 268)))
              (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 278) (instOfNatNat (nat_lit 278)))
                (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 282) (instOfNatNat (nat_lit 282)))
                  (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 284) (instOfNatNat (nat_lit 284)))))))))),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.TriePop.descend k) ∧ (∀ (address payload value : Nat) (items : List.{0} (Prod.{0, 0} Nat Nat))
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 264) (instOfNatNat (nat_lit 264)))) address →
      @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address
            (@List.cons.{0} (Prod.{0, 0} Nat Nat) (@Prod.mk.{0, 0} Nat Nat payload value) items)) →
        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address
              (@List.cons.{0} (Prod.{0, 0} Nat Nat) (@Prod.mk.{0, 0} Nat Nat payload value) items)) →
          And
            (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leafData s).natMem
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem address
                  (@List.length.{0} (Prod.{0, 0} Nat Nat) items))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (DecrAlmostLinearSSSP.Decremental.Exact.Payload.root items)))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leafData s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))))
                value)
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leafData s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))))
                (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Exact.TriePop.leafData s).realMem s.realMem))))))))))) := by sorry
