-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_7
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:13:16.65531+00:00
-- url     : https://prove2.me/theorems/2843ab0b-ce51-47fc-9017-9594e5bc163f
-- title:
--   Native Dijkstra relaxation and linked-list scan contracts
-- statement:
--   This collection gives the universally quantified contracts for native dijkstra relaxation and linked-list scan contracts. All graph identifiers, queue keys, payloads, registers and addresses are finite natural indices; capacities and arithmetic registers use the scalar RAM types defined in the accompanying interface.
--
--   Native queue operations, strict label improvements, active-edge tests, settled-vertex guards and linked-list traversal preserve the full Dijkstra memory image. Each outgoing-edge scan realizes the mathematical relaxation sequence while maintaining the extracted minimum as a ghost queue entry. The contracts specify all modified registers and memory cells and charge the scan by its original outgoing degree and trie height.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_7 : (((((((∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue s →
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j h →
        @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base j ∉
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h tree) ∧ (∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue s →
    @Eq.{1} Nat
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract h tree))
      (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) queue))) ∧ ((∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue s →
    ∀ (key : Nat) (v : Fin n),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))) key →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262)))) (@Fin.val n v) →
          @LT.lt.{0} Nat instLTNat key
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h) →
            ∃ cost t next,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code s
                  cost t)
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 43) (instOfNatNat (nat_lit 43)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (And
                    (@DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot next
                      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) queue) t)
                    (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                      (∀ (a : Nat), @LT.lt.{0} Nat instLTNat a slot → @Eq.{1} Nat (t.natMem a) (s.natMem a)))))) ∧ (∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue s →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) queue) →
      ∃ cost t next key v remaining,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code s cost
            t)
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) h
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (And (@DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot next remaining t)
              (And (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))) key)
                (And
                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))))
                    (@Fin.val n v))
                  (And
                    (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) queue
                      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) remaining))
                    (And
                      (∀ (item : Prod.{0, 0} Nat (Fin n)),
                        @Membership.mem.{0, 0} (Prod.{0, 0} Nat (Fin n)) (Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
                            (@Multiset.instMembership.{0} (Prod.{0, 0} Nat (Fin n))) queue item →
                          @LE.le.{0} Nat instLENat key (@Prod.fst.{0, 0} Nat (Fin n) item))
                      (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                        (∀ (a : Nat), @LT.lt.{0} Nat instLTNat a slot → @Eq.{1} Nat (t.natMem a) (s.natMem a)))))))))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (v : Fin i.n),
  @LT.lt.{0} Nat instLTNat (@Fin.val i.n v) (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapSlot i)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (v : Fin i.n),
  @LT.lt.{0} Nat instLTNat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i).settled (@Fin.val i.n v))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapSlot i))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (v : Fin i.n),
  @LT.lt.{0} Nat instLTNat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i).distances (@Fin.val i.n v))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapSlot i)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (e : Fin i.k),
  @LT.lt.{0} Nat instLTNat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i).active (@Fin.val i.k e))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapSlot i)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Nat),
  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.staticFootprint i
        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i))
      a →
    @LT.lt.{0} Nat instLTNat a (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapSlot i)))))) ∧ ((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree next :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue remaining : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image i.n
        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapBase i)
        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapSlot i) next remaining t →
      (∀ (j : Nat),
          @LT.lt.{0} Nat instLTNat j (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))) →
            @Eq.{1} Nat (t.natReg j) (s.natReg j)) →
        @Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
            (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))) →
          @Eq.{1} (Nat → Real) t.realMem s.realMem →
            (∀ (a : Nat),
                @LT.lt.{0} Nat instLTNat a (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapSlot i) →
                  @Eq.{1} Nat (t.natMem a) (s.natMem a)) →
              DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled next remaining t) ∧ (∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue s →
    (∀ (j : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
            (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
              (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))
                (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 236) (instOfNatNat (nat_lit 236)))
                  (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 238) (instOfNatNat (nat_lit 238)))
                    (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))
                      (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246)))))))))
            j →
          @Eq.{1} Nat (t.natReg j) (s.natReg j)) →
      @Eq.{1} (Nat → Nat) t.natMem s.natMem →
        @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue t)) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    (∀ (j : Nat),
        @LE.le.{0} Nat instLENat j (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246))) →
          @Eq.{1} Nat (t.natReg j) (s.natReg j)) →
      @Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))) →
        @Eq.{1} (Nat → Nat) t.natMem s.natMem →
          @Eq.{1} (Nat → Real) t.realMem s.realMem →
            DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue t) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    ∃ c,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.queueCount s c
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.counted s))
        (@LE.le.{0} Nat instLENat c (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))))) ∧ (((∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 346) (instOfNatNat (nat_lit 346))) →
    @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 348) (instOfNatNat (nat_lit 348))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.queueCount j) ∧ (∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.queueCount j)) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∃ c,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.queueCount s c
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.counted s))
        (And (@LE.le.{0} Nat instLENat c (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
          (And
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.counted s))
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.counted s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 348) (instOfNatNat (nat_lit 348))))
              (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin i.n)) queue))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidateAtoms))
    s (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidateData s)) ∧ (∀
  j ∉
    @Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 312) (instOfNatNat (nat_lit 312)))
      (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 316) (instOfNatNat (nat_lit 316)))
        (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 322) (instOfNatNat (nat_lit 322)))
          (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 324) (instOfNatNat (nat_lit 324)))
            (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 326) (instOfNatNat (nat_lit 326)))
              (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                (@OfNat.ofNat.{0} Nat (nat_lit 336) (instOfNatNat (nat_lit 336)))))))),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidateAtoms))
    j)))))) ∧ (((((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidateAtoms))
    j) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (e : Fin i.k) (key : Nat),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
          (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) i.k e) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310))))
            (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e)) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 304) (instOfNatNat (nat_lit 304)))) key →
            And
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue
                (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidateData s))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidateData s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310))))
                  (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e)))
                (And
                  (@Eq.{1} Nat
                    ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidateData s).natReg
                      (@OfNat.ofNat.{0} Nat (nat_lit 326) (instOfNatNat (nat_lit 326))))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (i.weight e)))
                  (And
                    (@Eq.{1} Nat
                      ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidateData s).natReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 316) (instOfNatNat (nat_lit 316))))
                      (s.natMem (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e))))
                    (And
                      (@Eq.{1} Nat
                        ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidateData s).natReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 322) (instOfNatNat (nat_lit 322))))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i).distances
                          (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e))))
                      (@Eq.{1} Nat
                        ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidateData s).natReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 324) (instOfNatNat (nat_lit 324))))
                        (s.natMem
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i).distances
                            (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e))))))))))) ∧ ((∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue s →
    (∀ (j : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
            (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
              (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))
                (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 236) (instOfNatNat (nat_lit 236)))
                  (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 238) (instOfNatNat (nat_lit 238)))
                    (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))
                      (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 246) (instOfNatNat (nat_lit 246)))))))))
            j →
          @Eq.{1} Nat (t.natReg j) (s.natReg j)) →
      (∀ (a : Nat), @LE.le.{0} Nat instLENat base a → @Eq.{1} Nat (t.natMem a) (s.natMem a)) →
        @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue t) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improveAtoms))
    s (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improved s)))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    And
      (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improved s).natMem
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 322) (instOfNatNat (nat_lit 322))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 326) (instOfNatNat (nat_lit 326))))))
      (And
        (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improved s).realMem
          (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310))))
            (@Nat.cast.{0} Real Real.instNatCast
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 326) (instOfNatNat (nat_lit 326)))))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improved s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 326) (instOfNatNat (nat_lit 326)))))
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improved s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))))
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310)))))))) ∧ (∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))) →
    @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
        (DecrAlmostLinearSSSP.Decremental.Structured.sequence
          (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
            DecrAlmostLinearSSSP.Decremental.Structured.Cmd DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
            DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improveAtoms))
        j)) ∧ ((∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 332) (instOfNatNat (nat_lit 332))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
      (DecrAlmostLinearSSSP.Decremental.Structured.sequence
        (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
          DecrAlmostLinearSSSP.Decremental.Structured.Cmd DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
          DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improveAtoms))
      j) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {tentative : Fin i.n → Option.{0} Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative s →
    ∀ (target : Fin i.n) (candidate : Nat),
      (∀ (v u : Fin i.n),
          @Ne.{1} Nat (@Fin.val i.n v)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.distances (@Fin.val i.n u))) →
        @Eq.{1} (Nat → Nat) t.natMem
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem (@Fin.val i.n target)
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.distances (@Fin.val i.n target))
              candidate) →
          @Eq.{1} (Nat → Real) t.realMem
              (@Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem (@Fin.val i.n target)
                (@Nat.cast.{0} Real Real.instNatCast candidate)) →
            DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l
              (@Function.update.{1, 1} (Fin i.n) (fun a => Option.{0} Nat) (instDecidableEqFin i.n) tentative target
                (@Option.some.{0} Nat candidate))
              t) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (target : Fin i.n) (candidate : Nat),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310)))) (@Fin.val i.n target) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 322) (instOfNatNat (nat_lit 322))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i).distances (@Fin.val i.n target)) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 326) (instOfNatNat (nat_lit 326)))) candidate →
            And
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted
                (@Function.update.{1, 1} (Fin i.n) (fun a => Option.{0} Nat) (instDecidableEqFin i.n) tentative target
                  (@Option.some.{0} Nat candidate))
                settled tree queue (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improved s))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improved s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260))))
                  candidate)
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improved s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))))
                  (@Fin.val i.n target)))))))) ∧ ((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (key : Nat) (v : Fin i.n),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))) key →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262)))) (@Fin.val i.n v) →
          @LT.lt.{0} Nat instLTNat key
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)) →
            ∃ cost t next,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePush.code s
                  cost t)
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 43) (instOfNatNat (nat_lit 43)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled next
                    (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin i.n)) (@Prod.mk.{0, 0} Nat (Fin i.n) key v) queue) t))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin i.n)) queue) →
      ∃ cost t next key v remaining,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.TriePop.code s cost
            t)
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 34) (instOfNatNat (nat_lit 34)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
            (And (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled next remaining t)
              (And (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 260) (instOfNatNat (nat_lit 260)))) key)
                (And
                  (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262))))
                    (@Fin.val i.n v))
                  (And
                    (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) queue
                      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin i.n)) (@Prod.mk.{0, 0} Nat (Fin i.n) key v) remaining))
                    (∀ (item : Prod.{0, 0} Nat (Fin i.n)),
                      @Membership.mem.{0, 0} (Prod.{0, 0} Nat (Fin i.n)) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                          (@Multiset.instMembership.{0} (Prod.{0, 0} Nat (Fin i.n))) queue item →
                        @LE.le.{0} Nat instLENat key (@Prod.fst.{0, 0} Nat (Fin i.n) item))))))))) ∧ ((∀ (j : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 300) (instOfNatNat (nat_lit 300))) j →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improve j) ∧ ((∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 332) (instOfNatNat (nat_lit 332))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improve j) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (target : Fin i.n) (candidate : Nat),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310)))) (@Fin.val i.n target) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 322) (instOfNatNat (nat_lit 322))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i).distances (@Fin.val i.n target)) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 326) (instOfNatNat (nat_lit 326)))) candidate →
            @LT.lt.{0} Nat instLTNat candidate
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)) →
              ∃ cost t next,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.improve s cost t)
                  (And
                    (@LE.le.{0} Nat instLENat cost
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 49) (instOfNatNat (nat_lit 49)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted
                      (@Function.update.{1, 1} (Fin i.n) (fun a => Option.{0} Nat) (instDecidableEqFin i.n) tentative
                        target (@Option.some.{0} Nat candidate))
                      settled next
                      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin i.n)) (@Prod.mk.{0, 0} Nat (Fin i.n) candidate target)
                        queue)
                      t)))))) ∧ (((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source : Fin n} {tentative : Fin n → Option.{0} Nat} {settled : Finset.{0} (Fin n)}
  {remaining : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} (key : Nat) (v : Fin n),
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled
      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) remaining) →
    @Eq.{1} (Option.{0} Nat) (tentative v) (@Option.some.{0} Nat key) →
      ∀ (e : Fin k),
        @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
            (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active e →
          @Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) v →
            @DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e ∉ settled →
              (∀ (d : Nat),
                  @Eq.{1} (Option.{0} Nat) (tentative (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e))
                      (@Option.some.{0} Nat d) →
                    @LT.lt.{0} Nat instLTNat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (w e))
                      d) →
                @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source
                  (@Function.update.{1, 1} (Fin n) (fun a => Option.{0} Nat) (instDecidableEqFin n) tentative
                    (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e)
                    (@Option.some.{0} Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (w e))))
                  settled
                  (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v)
                    (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n))
                      (@Prod.mk.{0, 0} Nat (Fin n)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (w e))
                        (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e))
                      remaining))) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source : Fin n} {tentative : Fin n → Option.{0} Nat} {settled : Finset.{0} (Fin n)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))},
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled queue →
    ∀ (v : Fin n) (key : Nat),
      @Eq.{1} (Option.{0} Nat) (tentative v) (@Option.some.{0} Nat key) →
        ∀ (e : Fin k),
          @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
              (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active e →
            @Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) v →
              @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n) (@Finset.instSetLike.{0} (Fin n)))
                  settled (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e) →
                ∃ d,
                  And
                    (@Eq.{1} (Option.{0} Nat) (tentative (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e))
                      (@Option.some.{0} Nat d))
                    (@LE.le.{0} Nat instLENat d
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (w e))))) ∧ ((∀ (old : Option.{0} Nat) (candidate : Nat),
  Iff (DecrAlmostLinearSSSP.Decremental.Exact.Improves old candidate)
    (∀ (d : Nat), @Eq.{1} (Option.{0} Nat) old (@Option.some.{0} Nat d) → @LT.lt.{0} Nat instLTNat candidate d)) ∧ ((∀ (old : Option.{0} Nat) (candidate : Nat),
  Not (DecrAlmostLinearSSSP.Decremental.Exact.Improves old candidate) →
    ∃ d, And (@Eq.{1} (Option.{0} Nat) old (@Option.some.{0} Nat d)) (@LE.le.{0} Nat instLENat d candidate)) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source : Fin n} {tentative : Fin n → Option.{0} Nat} {settled : Finset.{0} (Fin n)}
  {remaining : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} (key : Nat) (v : Fin n),
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled
      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) remaining) →
    @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
        (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n) (@Finset.instSetLike.{0} (Fin n))) settled v →
      @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled remaining))))))) ∧ ((((((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source v : Fin n} {key : Nat} {settled : Finset.{0} (Fin n)} {tentative : Fin n → Option.{0} Nat}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))},
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled
      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) queue) →
    v ∉ settled →
      (∀ (item : Prod.{0, 0} Nat (Fin n)),
          @Membership.mem.{0, 0} (Prod.{0, 0} Nat (Fin n)) (Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
              (@Multiset.instMembership.{0} (Prod.{0, 0} Nat (Fin n))) queue item →
            @LE.le.{0} Nat instLENat key (@Prod.fst.{0, 0} Nat (Fin n) item)) →
        @DecrAlmostLinearSSSP.Decremental.Exact.ScanState n k g active w source v key settled (@List.nil.{0} (Fin k))
          tentative queue) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source v : Fin n} {key : Nat} {settled : Finset.{0} (Fin n)} {scanned : List.{0} (Fin k)}
  {tentative : Fin n → Option.{0} Nat} {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))},
  @DecrAlmostLinearSSSP.Decremental.Exact.ScanState n k g active w source v key settled scanned tentative queue →
    v ∉ settled →
      (∀ (e : Fin k),
          @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
              (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active e →
            @Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) v →
              @Membership.mem.{0, 0} (Fin k) (List.{0} (Fin k)) (@List.instMembership.{0} (Fin k)) scanned e) →
        @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative
          (@Insert.insert.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instInsert.{0} (Fin n) (instDecidableEqFin n)) v
            settled)
          queue)) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (e : Fin i.k) (key : Nat),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
          (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) i.k e) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310))))
            (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e)) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 304) (instOfNatNat (nat_lit 304)))) key →
            @Membership.mem.{0, 0} (Fin i.k) (Finset.{0} (Fin i.k))
                (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin i.k)) (Fin i.k) (@Finset.instSetLike.{0} (Fin i.k)))
                (@DecrAlmostLinearSSSP.Decremental.live i.k deleted) e →
              @DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e ∉ settled →
                @LT.lt.{0} Nat instLTNat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (i.weight e))
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)) →
                  have result :=
                    @DecrAlmostLinearSSSP.Decremental.Exact.relax i.n i.k i.graph
                      (@DecrAlmostLinearSSSP.Decremental.live i.k deleted) i.weight settled key e tentative queue;
                  ∃ cost t next,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidate s cost t)
                      (And
                        (@LE.le.{0} Nat instLENat cost
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 60) (instOfNatNat (nat_lit 60)))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted
                          (@Prod.fst.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                            result)
                          settled next
                          (@Prod.snd.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n)))
                            result)
                          t))) ∧ (∀ (j : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 300) (instOfNatNat (nat_lit 300))) j →
    j ∉
        @Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 312) (instOfNatNat (nat_lit 312)))
          (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 316) (instOfNatNat (nat_lit 316)))
            (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 322) (instOfNatNat (nat_lit 322)))
              (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 324) (instOfNatNat (nat_lit 324)))
                (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 326) (instOfNatNat (nat_lit 326)))
                  (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 336) (instOfNatNat (nat_lit 336)))))))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidate j))) ∧ (((∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 332) (instOfNatNat (nat_lit 332))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.candidate j) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeader s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeaderData s))) ∧ ((∀
  j ∉
    @Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310)))
      (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 314) (instOfNatNat (nat_lit 314)))
        (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 316) (instOfNatNat (nat_lit 316)))
          (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
            (@OfNat.ofNat.{0} Nat (nat_lit 336) (instOfNatNat (nat_lit 336)))))),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeader j) ∧ ((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeader j) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (e : Fin i.k),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
          (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) i.k e) →
        And
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeaderData s))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeaderData s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310))))
              (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e)))
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeaderData s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 316) (instOfNatNat (nat_lit 316))))
              (@ite.{1} Nat
                (@Membership.mem.{0, 0} (Fin i.k) (Finset.{0} (Fin i.k))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin i.k)) (Fin i.k) (@Finset.instSetLike.{0} (Fin i.k)))
                  (@DecrAlmostLinearSSSP.Decremental.live i.k deleted) e)
                (@Finset.decidableMem.{0} (Fin i.k) (instDecidableEqFin i.k) e
                  (@DecrAlmostLinearSSSP.Decremental.live i.k deleted))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))) ∧ ((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.targetSettledAtoms))
    s (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.targetData s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.nextAtoms))
    s (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.nextData s))) ∧ ((∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 318) (instOfNatNat (nat_lit 318))) →
    @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 320) (instOfNatNat (nat_lit 320))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
        (DecrAlmostLinearSSSP.Decremental.Structured.sequence
          (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
            DecrAlmostLinearSSSP.Decremental.Structured.Cmd DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
            DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.targetSettledAtoms))
        j) ∧ ((∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))) →
    @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 336) (instOfNatNat (nat_lit 336))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
        (DecrAlmostLinearSSSP.Decremental.Structured.sequence
          (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
            DecrAlmostLinearSSSP.Decremental.Structured.Cmd DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
            DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.nextAtoms))
        j) ∧ (∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.targetSettledAtoms))
    j)))) ∧ (((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.nextAtoms))
    j) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (v : Fin i.n),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310)))) (@Fin.val i.n v) →
        And
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.targetData s))
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.targetData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 320) (instOfNatNat (nat_lit 320))))
            (@ite.{1} Nat
              (@Membership.mem.{0, 0} (Fin i.n) (Finset.{0} (Fin i.n))
                (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin i.n)) (Fin i.n) (@Finset.instSetLike.{0} (Fin i.n)))
                settled v)
              (@Finset.decidableMem.{0} (Fin i.n) (instDecidableEqFin i.n) v settled)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (e : Fin i.k),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
          (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) i.k e) →
        And
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.nextData s))
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.nextData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
            (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.root
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) i.k
              (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency i.n i.k i.graph (@Fin.val i.k e)
                (@DecrAlmostLinearSSSP.Decremental.Digraph.tail i.n i.k i.graph e))))) ∧ ((∀ (j : Nat),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 300) (instOfNatNat (nat_lit 300))) j →
    j ∉
        @Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 312) (instOfNatNat (nat_lit 312)))
          (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 316) (instOfNatNat (nat_lit 316)))
            (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 318) (instOfNatNat (nat_lit 318)))
              (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 320) (instOfNatNat (nat_lit 320)))
                (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 322) (instOfNatNat (nat_lit 322)))
                  (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 324) (instOfNatNat (nat_lit 324)))
                    (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 326) (instOfNatNat (nat_lit 326)))
                      (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 336) (instOfNatNat (nat_lit 336)))))))))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeGuard j) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (e : Fin i.k) (key : Nat),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
          (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) i.k e) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310))))
            (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e)) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 304) (instOfNatNat (nat_lit 304)))) key →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 316) (instOfNatNat (nat_lit 316))))
                (@ite.{1} Nat
                  (@Membership.mem.{0, 0} (Fin i.k) (Finset.{0} (Fin i.k))
                    (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin i.k)) (Fin i.k)
                      (@Finset.instSetLike.{0} (Fin i.k)))
                    (@DecrAlmostLinearSSSP.Decremental.live i.k deleted) e)
                  (@Finset.decidableMem.{0} (Fin i.k) (instDecidableEqFin i.k) e
                    (@DecrAlmostLinearSSSP.Decremental.live i.k deleted))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
              @LT.lt.{0} Nat instLTNat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (i.weight e))
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)) →
                have r :=
                  @DecrAlmostLinearSSSP.Decremental.Exact.relax i.n i.k i.graph
                    (@DecrAlmostLinearSSSP.Decremental.live i.k deleted) i.weight settled key e tentative queue;
                ∃ cost t next,
                  And
                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                      DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeGuard s cost t)
                    (And
                      (@LE.le.{0} Nat instLENat cost
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted
                        (@Prod.fst.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) r)
                        settled next
                        (@Prod.snd.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) r) t)))))))) ∧ (((((∀ {s u v t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {a b c : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeader s a u →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeGuard u b v →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval
          (DecrAlmostLinearSSSP.Decremental.Structured.sequence
            (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
              DecrAlmostLinearSSSP.Decremental.Structured.Cmd DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
              DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.nextAtoms))
          v c t →
        DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeBody s
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b) c)
          t) ∧ (∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeHeader j →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeGuard j →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
          (DecrAlmostLinearSSSP.Decremental.Structured.sequence
            (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
              DecrAlmostLinearSSSP.Decremental.Structured.Cmd DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
              DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.nextAtoms))
          j →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeBody j)) ∧ ((DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeBody
  (@OfNat.ofNat.{0} Nat (nat_lit 304) (instOfNatNat (nat_lit 304)))) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeBody
  (@OfNat.ofNat.{0} Nat (nat_lit 306) (instOfNatNat (nat_lit 306)))))) ∧ (((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (e : Fin i.k) (key : Nat),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
          (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) i.k e) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 304) (instOfNatNat (nat_lit 304)))) key →
          @LT.lt.{0} Nat instLTNat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (i.weight e))
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)) →
            have r :=
              @DecrAlmostLinearSSSP.Decremental.Exact.relax i.n i.k i.graph
                (@DecrAlmostLinearSSSP.Decremental.live i.k deleted) i.weight settled key e tentative queue;
            ∃ cost t next,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeBody s cost t)
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80)))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                  (And
                    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted
                      (@Prod.fst.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) r) settled
                      next (@Prod.snd.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) r) t)
                    (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
                      (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.root
                        (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) i.k
                        (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency i.n i.k i.graph (@Fin.val i.k e)
                          (@DecrAlmostLinearSSSP.Decremental.Digraph.tail i.n i.k i.graph e))))))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i l s →
    DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i l t →
      ∀ (es : List.{0} (Fin i.k)),
        @DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Chain i.k l s es →
          @DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Chain i.k l t es)) ∧ ((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source v : Fin n} {key : Nat} {settled : Finset.{0} (Fin n)} {scanned : List.{0} (Fin k)}
  {tentative : Fin n → Option.{0} Nat} {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))},
  @DecrAlmostLinearSSSP.Decremental.Exact.ScanState n k g active w source v key settled scanned tentative queue →
    ∀ (e : Fin k),
      @Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) v →
        have result := @DecrAlmostLinearSSSP.Decremental.Exact.relax n k g active w settled key e tentative queue;
        And
          (@DecrAlmostLinearSSSP.Decremental.Exact.ScanState n k g active w source v key settled
            (@List.cons.{0} (Fin k) e scanned)
            (@Prod.fst.{0, 0} (Fin n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) result)
            (@Prod.snd.{0, 0} (Fin n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) result))
          (@LE.le.{0} Nat instLENat
            (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n))
              (@Prod.snd.{0, 0} (Fin n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) result))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) queue)
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) ∧ ((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source v : Fin n} {key : Nat} {settled : Finset.{0} (Fin n)} {scanned : List.{0} (Fin k)}
  {tentative : Fin n → Option.{0} Nat} {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))},
  @DecrAlmostLinearSSSP.Decremental.Exact.ScanState n k g active w source v key settled scanned tentative queue →
    ∀ (es : List.{0} (Fin k)),
      (∀ (e : Fin k),
          @Membership.mem.{0, 0} (Fin k) (List.{0} (Fin k)) (@List.instMembership.{0} (Fin k)) es e →
            @Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) v) →
        have r := @DecrAlmostLinearSSSP.Decremental.Exact.scanEdges n k g active w settled key es tentative queue;
        And
          (@DecrAlmostLinearSSSP.Decremental.Exact.ScanState n k g active w source v key settled
            (@HAppend.hAppend.{0, 0, 0} (List.{0} (Fin k)) (List.{0} (Fin k)) (List.{0} (Fin k))
              (@instHAppendOfAppend.{0} (List.{0} (Fin k)) (@List.instAppend.{0} (Fin k)))
              (@List.reverse.{0} (Fin k) es) scanned)
            (@Prod.fst.{0, 0} (Fin n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) r)
            (@Prod.snd.{0, 0} (Fin n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) r))
          (@LE.le.{0} Nat instLENat
            (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n))
              (@Prod.snd.{0, 0} (Fin n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) r))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) queue) (@List.length.{0} (Fin k) es)))) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source v : Fin n} {key : Nat} {settled : Finset.{0} (Fin n)} {tentative : Fin n → Option.{0} Nat}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))},
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled
      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) queue) →
    v ∉ settled →
      (∀ (item : Prod.{0, 0} Nat (Fin n)),
          @Membership.mem.{0, 0} (Prod.{0, 0} Nat (Fin n)) (Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
              (@Multiset.instMembership.{0} (Prod.{0, 0} Nat (Fin n))) queue item →
            @LE.le.{0} Nat instLENat key (@Prod.fst.{0, 0} Nat (Fin n) item)) →
        have r :=
          @DecrAlmostLinearSSSP.Decremental.Exact.scanEdges n k g active w settled key
            (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g k v) tentative queue;
        And
          (@DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source
            (@Prod.fst.{0, 0} (Fin n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) r)
            (@Insert.insert.{0, 0} (Fin n) (Finset.{0} (Fin n)) (@Finset.instInsert.{0} (Fin n) (instDecidableEqFin n))
              v settled)
            (@Prod.snd.{0, 0} (Fin n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) r))
          (@LE.le.{0} Nat instLENat
            (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n))
              (@Prod.snd.{0, 0} (Fin n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) r))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) queue)
              (@List.length.{0} (Fin k) (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g k v))))))))) ∧ ((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (key : Nat) (es : List.{0} (Fin i.k)),
      @DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Chain i.k
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) s es →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
            (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.root
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) i.k es) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 304) (instOfNatNat (nat_lit 304)))) key →
            (∀ (e : Fin i.k),
                @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k)) es e →
                  @LT.lt.{0} Nat instLTNat
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (i.weight e))
                    (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                      (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i))) →
              have r :=
                @DecrAlmostLinearSSSP.Decremental.Exact.scanEdges i.n i.k i.graph
                  (@DecrAlmostLinearSSSP.Decremental.live i.k deleted) i.weight settled key es tentative queue;
              ∃ cost t next,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.edgeLoop s cost t)
                  (And
                    (@LE.le.{0} Nat instLENat cost
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82)))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          (@List.length.{0} (Fin i.k) es))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (And
                      (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted
                        (@Prod.fst.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) r)
                        settled next
                        (@Prod.snd.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) r) t)
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.settleAtoms))
    s (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.settledData s))) ∧ ((∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 318) (instOfNatNat (nat_lit 318))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.Structured.sequence
        (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
          DecrAlmostLinearSSSP.Decremental.Structured.Cmd DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
          DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.settleAtoms))
      j) ∧ ((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.settleAtoms))
    j) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (v : Fin i.n),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 306) (instOfNatNat (nat_lit 306)))) (@Fin.val i.n v) →
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative
          (@Insert.insert.{0, 0} (Fin i.n) (Finset.{0} (Fin i.n))
            (@Finset.instInsert.{0} (Fin i.n) (instDecidableEqFin i.n)) v settled)
          tree queue (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.settledData s))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.scanPrepareAtoms))
    s (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.scanPrepared s)) ∧ (∀ (j : Nat),
  @Ne.{1} Nat j (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      (DecrAlmostLinearSSSP.Decremental.Structured.sequence
        (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom
          DecrAlmostLinearSSSP.Decremental.Structured.Cmd DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
          DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.scanPrepareAtoms))
      j)) ∧ ((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom
        DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.scanPrepareAtoms))
    j) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (v : Fin i.n),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 306) (instOfNatNat (nat_lit 306)))) (@Fin.val i.n v) →
        And
          (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue
            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.scanPrepared s))
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.scanPrepared s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308))))
            (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.root
              (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.layout i) i.k
              (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency i.n i.k i.graph i.k v)))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {deleted : List.{0} (Fin i.k)} {tentative : Fin i.n → Option.{0} Nat}
  {settled : Finset.{0} (Fin i.n)}
  {tree :
    DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted tentative settled tree queue s →
    ∀ (v : Fin i.n) (key : Nat),
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 306) (instOfNatNat (nat_lit 306)))) (@Fin.val i.n v) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 304) (instOfNatNat (nat_lit 304)))) key →
          (∀ (e : Fin i.k),
              @Membership.mem.{0, 0} (Fin i.k) (List.{0} (Fin i.k)) (@List.instMembership.{0} (Fin i.k))
                  (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency i.n i.k i.graph i.k v) e →
                @LT.lt.{0} Nat instLTNat
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (i.weight e))
                  (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                    (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i))) →
            have r :=
              @DecrAlmostLinearSSSP.Decremental.Exact.scanEdges i.n i.k i.graph
                (@DecrAlmostLinearSSSP.Decremental.live i.k deleted) i.weight settled key
                (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency i.n i.k i.graph i.k v) tentative queue;
            ∃ cost t next,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.scan s
                  cost t)
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82)))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.heapHeight i)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                        (@List.length.{0} (Fin i.k)
                          (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency i.n i.k i.graph i.k v)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                  (DecrAlmostLinearSSSP.Decremental.Exact.Dijkstra.Memory i deleted
                    (@Prod.fst.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) r)
                    (@Insert.insert.{0, 0} (Fin i.n) (Finset.{0} (Fin i.n))
                      (@Finset.instInsert.{0} (Fin i.n) (instDecidableEqFin i.n)) v settled)
                    next (@Prod.snd.{0, 0} (Fin i.n → Option.{0} Nat) (Multiset.{0} (Prod.{0, 0} Nat (Fin i.n))) r) t)))))))))) := by sorry
