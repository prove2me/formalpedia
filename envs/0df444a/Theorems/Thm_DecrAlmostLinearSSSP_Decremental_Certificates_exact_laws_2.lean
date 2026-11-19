-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_2
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:13:06.29565+00:00
-- url     : https://prove2.me/theorems/7de36fac-06f0-4f5b-8328-e12312c2951c
-- title:
--   Charged structured compilation and queue allocation
-- statement:
--   This collection gives the universally quantified contracts for charged structured compilation and queue allocation. All graph identifiers, queue keys, payloads, registers and addresses are finite natural indices; capacities and arithmetic registers use the scalar RAM types defined in the accompanying interface.
--
--   A terminating finite execution can be compressed to its actual work increment. Structured sequencing, branches and loops compile to instruction lists with the specified lengths and locations. Each structured evaluation is realized by actual scalar RAM execution with its charged cost, and the stored-array query routine uses nine charged instructions. Radix-trie node and payload allocation creates the stated finite memory image and preserves disjoint cells.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_2 : (((((((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  @LE.le.{0} Nat instLENat c.work (DecrAlmostLinearSSSP.Decremental.execute p c t).work) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c t).halted Bool.true →
    ∃ r,
      And (@LE.le.{0} Nat instLENat r t)
        (And
          (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.execute p c r)
            (DecrAlmostLinearSSSP.Decremental.execute p c t))
          (@Eq.{1} Nat r
            (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
              (DecrAlmostLinearSSSP.Decremental.execute p c t).work c.work))))) ∧ ((∀ (host guest : DecrAlmostLinearSSSP.Decremental.Program) (offset returnPC : Nat),
  DecrAlmostLinearSSSP.Decremental.EmbedsCode host guest offset returnPC →
    ∀ (c final : DecrAlmostLinearSSSP.Decremental.Machine),
      @Eq.{1} Bool c.halted Bool.false →
        @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat c.pc
              (DecrAlmostLinearSSSP.Decremental.embeddedDestination offset returnPC
                (DecrAlmostLinearSSSP.Decremental.decodeGuest c)) →
            DecrAlmostLinearSSSP.Decremental.Ends guest (DecrAlmostLinearSSSP.Decremental.decodeGuest c) final →
              ∃ steps d,
                And
                  (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                    (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                  (And
                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                      final)
                    (And (@Eq.{1} Nat d.pc returnPC)
                      (And
                        (@LE.le.{0} Nat instLENat d.work
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) final.work
                                (DecrAlmostLinearSSSP.Decremental.decodeGuest c).work))))
                        (And (@Eq.{1} Bool d.halted Bool.false)
                          (And
                            (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                            (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      DecrAlmostLinearSSSP.Decremental.Straight ins →
        And
          (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.step p c).pc
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (And (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.step p c).halted Bool.false)
            (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.step p c).work
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))) ∧ (((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (n : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    (∀ (j : Nat),
        @LT.lt.{0} Nat instLTNat j n →
          ∃ ins,
            And
              (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                  DecrAlmostLinearSSSP.Decremental.Instruction
                  (fun as i =>
                    @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                  (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc j))
                (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins))
              (DecrAlmostLinearSSSP.Decremental.Straight ins)) →
      ∀ (j : Nat),
        @LE.le.{0} Nat instLENat j n →
          And
            (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.execute p c j).pc
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc j))
            (And (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c j).halted Bool.false)
              (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.execute p c j).work
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work j)))) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      Not (DecrAlmostLinearSSSP.Decremental.ModifiesMemory ins) →
        And (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.step p c).realMem c.realMem)
          (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.step p c).natMem c.natMem))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  (∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j t →
        ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
                (DecrAlmostLinearSSSP.Decremental.execute p c j).pc)
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
            Not (DecrAlmostLinearSSSP.Decremental.ModifiesMemory ins)) →
    And (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.execute p c t).realMem c.realMem)
      (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.execute p c t).natMem c.natMem)) ∧ ((∀ (c : DecrAlmostLinearSSSP.Decremental.Structured.Cmd) (start : Nat),
  @Eq.{1} Nat
    (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction
      (DecrAlmostLinearSSSP.Decremental.Structured.compile c start))
    (DecrAlmostLinearSSSP.Decremental.Structured.codeSize c)) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction a.instruction) →
      And
        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data
          (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.step p c))
          (a.effect (DecrAlmostLinearSSSP.Decremental.Structured.data c)))
        (And
          (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.step p c).pc
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (And (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.step p c).halted Bool.false)
            (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.step p c).work
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))) ∧ ((((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (test : DecrAlmostLinearSSSP.Decremental.Structured.Test) (target : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction (test.emit target)) →
      And
        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data
          (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.step p c))
          (DecrAlmostLinearSSSP.Decremental.Structured.data c))
        (And
          (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.step p c).pc
            (@ite.{1} Nat (test.holds (DecrAlmostLinearSSSP.Decremental.Structured.data c))
              (Classical.propDecidable (test.holds (DecrAlmostLinearSSSP.Decremental.Structured.data c))) target
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
          (And (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.step p c).halted Bool.false)
            (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.step p c).work
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) ∧ (∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {items : List.{0} (Prod.{0, 0} Nat Nat)},
  DecrAlmostLinearSSSP.Decremental.Exact.Payload.Image s items →
    (∀ (address : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
            (DecrAlmostLinearSSSP.Decremental.Exact.Payload.footprint items) address →
          @Eq.{1} Nat (t.natMem address) (s.natMem address)) →
      DecrAlmostLinearSSSP.Decremental.Exact.Payload.Image t items)) ∧ ((∀ {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {height : Nat}
  {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s height tree →
    (∀ (address : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
            (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint height tree) address →
          @Eq.{1} Nat (t.natMem address) (s.natMem address)) →
      @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image t height tree) ∧ (∀ {height : Nat} (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height),
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated height tree →
    Iff
      (@Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Ne.{1} (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height) tree
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.empty height))))) ∧ (((∀ {s : DecrAlmostLinearSSSP.Decremental.Structured.Data} {height : Nat}
  {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Image s height tree →
    @Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Eq.{1} Nat (s.natMem (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree))
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height
          (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.abstract height tree))) ∧ (∀ {height : Nat} (tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height),
  @Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint height tree)
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree))) ∧ ((∀ {height : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height} {low high : Nat},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded height tree low high →
    @Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      And (@LE.le.{0} Nat instLENat low (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree))
        (@LT.lt.{0} Nat instLTNat (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.root height tree) high)) ∧ ((∀ {height : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height} {low high low' high' : Nat},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded height tree low high →
    @LE.le.{0} Nat instLENat low' low →
      @LE.le.{0} Nat instLENat high high' →
        @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Bounded height tree low' high') ∧ (∀ {height : Nat} (address : Nat) (left right : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height)
  (offset : Nat),
  @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) height
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.node height address left right))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address offset))))))) ∧ (((((∀ (address : Nat) (items : List.{0} (Prod.{0, 0} Nat Nat)) (offset : Nat),
  @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
    @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address items))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address offset)) ∧ (∀ {height : Nat} (address : Nat) (left right : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height),
  @LE.le.{0} (Finset.{0} Nat)
    (@Preorder.toLE.{0} (Finset.{0} Nat)
      (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint height left)
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) height
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.node height address left right)))) ∧ ((∀ {height : Nat} (address : Nat) (left right : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height),
  @LE.le.{0} (Finset.{0} Nat)
    (@Preorder.toLE.{0} (Finset.{0} Nat)
      (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint height right)
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) height
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.node height address left right))) ∧ (∀ (address : Nat) (items : List.{0} (Prod.{0, 0} Nat Nat)),
  @LE.le.{0} (Finset.{0} Nat)
    (@Preorder.toLE.{0} (Finset.{0} Nat)
      (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Payload.footprint items)
    (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.leaf address items))))) ∧ (((∀ {height address : Nat} {left right : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) height
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.node height address left right) →
    ∀ (offset : Nat),
      @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address offset ∉
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint height left) ∧ (∀ {height address : Nat} {left right : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie height},
  @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.Separated
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) height
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.node height address left right) →
    ∀ (offset : Nat),
      @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) address offset ∉
          @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint height right)) ∧ ((∀ (old : Finset.{0} Nat) (fresh length : Nat),
  (∀ (address : Nat),
      @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
          (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) old address →
        @LT.lt.{0} Nat instLTNat address fresh) →
    @Disjoint.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat) (@Finset.instOrderBot.{0} Nat) old
      (@Finset.Ico.{0} Nat Nat.instPreorder Nat.instLocallyFiniteOrder fresh
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) fresh length))) ∧ ((∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {start : Nat}
  {a b : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction},
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (@HAppend.hAppend.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@instHAppendOfAppend.{0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@List.instAppend.{0} DecrAlmostLinearSSSP.Decremental.Instruction))
        a b) →
    DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start a) ∧ (∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {start : Nat}
  {a b : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction},
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (@HAppend.hAppend.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@instHAppendOfAppend.{0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@List.instAppend.{0} DecrAlmostLinearSSSP.Decremental.Instruction))
        a b) →
    DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
        (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction a))
      b))))) ∧ ((((∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {start : Nat} {ins : DecrAlmostLinearSSSP.Decremental.Instruction}
  {rest : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction},
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins rest) →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
        DecrAlmostLinearSSSP.Decremental.Instruction
        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code start)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins)) ∧ (∀ {p : DecrAlmostLinearSSSP.Decremental.Program} {start : Nat} {ins : DecrAlmostLinearSSSP.Decremental.Instruction}
  {rest : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction},
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins rest) →
    DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      rest)) ∧ ((∀ (codePrefix code suffix : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
  (p : DecrAlmostLinearSSSP.Decremental.Program),
  @Eq.{1} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
      (@HAppend.hAppend.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@instHAppendOfAppend.{0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@List.instAppend.{0} DecrAlmostLinearSSSP.Decremental.Instruction))
        codePrefix
        (@HAppend.hAppend.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@instHAppendOfAppend.{0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@List.instAppend.{0} DecrAlmostLinearSSSP.Decremental.Instruction))
          code suffix)) →
    DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p
      (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction codePrefix) code) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (start : Nat) (a b : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (DecrAlmostLinearSSSP.Decremental.Structured.compile (a.seq b) start) →
    And
      (DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
        (DecrAlmostLinearSSSP.Decremental.Structured.compile a start))
      (DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
          (DecrAlmostLinearSSSP.Decremental.Structured.codeSize a))
        (DecrAlmostLinearSSSP.Decremental.Structured.compile b
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
            (DecrAlmostLinearSSSP.Decremental.Structured.codeSize a))))) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (start : Nat) (test : DecrAlmostLinearSSSP.Decremental.Structured.Test)
  (yes no : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (DecrAlmostLinearSSSP.Decremental.Structured.compile
        (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.branch test yes no) start) →
    And
      (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code start)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
          (test.emit
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                (DecrAlmostLinearSSSP.Decremental.Structured.codeSize no))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
      (And
        (DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (DecrAlmostLinearSSSP.Decremental.Structured.compile no
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
        (And
          (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (DecrAlmostLinearSSSP.Decremental.Structured.codeSize no)))
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.jump
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                      (DecrAlmostLinearSSSP.Decremental.Structured.codeSize no))
                    (DecrAlmostLinearSSSP.Decremental.Structured.codeSize yes))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
          (DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                (DecrAlmostLinearSSSP.Decremental.Structured.codeSize no))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (DecrAlmostLinearSSSP.Decremental.Structured.compile yes
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                  (DecrAlmostLinearSSSP.Decremental.Structured.codeSize no))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))) ∧ (((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (start : Nat) (test : DecrAlmostLinearSSSP.Decremental.Structured.Test)
  (body : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
      (DecrAlmostLinearSSSP.Decremental.Structured.compile
        (DecrAlmostLinearSSSP.Decremental.Structured.Cmd.loop test body) start) →
    And
      (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code start)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
          (test.emit
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
      (And
        (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            (DecrAlmostLinearSSSP.Decremental.Instruction.jump
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                  (DecrAlmostLinearSSSP.Decremental.Structured.codeSize body))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
        (And
          (DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (DecrAlmostLinearSSSP.Decremental.Structured.compile body
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (DecrAlmostLinearSSSP.Decremental.Structured.codeSize body)))
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.jump start)))))) ∧ (∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc work : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data
    (DecrAlmostLinearSSSP.Decremental.Structured.data
      { pc := pc, realReg := c.realReg, natReg := c.natReg, realMem := c.realMem, natMem := c.natMem,
        halted := c.halted, fault := c.fault, work := work })
    (DecrAlmostLinearSSSP.Decremental.Structured.data c))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (target : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
          (DecrAlmostLinearSSSP.Decremental.Instruction.jump target)) →
      And
        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data
          (DecrAlmostLinearSSSP.Decremental.Structured.data
            (DecrAlmostLinearSSSP.Decremental.execute p c
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (DecrAlmostLinearSSSP.Decremental.Structured.data c))
        (And
          (@Eq.{1} Nat
            (DecrAlmostLinearSSSP.Decremental.execute p c
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).pc
            target)
          (And
            (@Eq.{1} Bool
              (DecrAlmostLinearSSSP.Decremental.execute p c
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).halted
              Bool.false)
            (@Eq.{1} Nat
              (DecrAlmostLinearSSSP.Decremental.execute p c
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).work
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) ∧ ((∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (start : Nat) (c : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
          (DecrAlmostLinearSSSP.Decremental.Structured.compile cmd start) →
        @Eq.{1} Nat c.pc start →
          @Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data (DecrAlmostLinearSSSP.Decremental.Structured.data c)
              s →
            @Eq.{1} Bool c.halted Bool.false →
              And
                (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data
                  (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.execute p c cost))
                  t)
                (And
                  (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.execute p c cost).pc
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                      (DecrAlmostLinearSSSP.Decremental.Structured.codeSize cmd)))
                  (And (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c cost).halted Bool.false)
                    (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.execute p c cost).work
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work cost))))) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  DecrAlmostLinearSSSP.Decremental.FaultWellFormed c →
    DecrAlmostLinearSSSP.Decremental.FaultWellFormed (DecrAlmostLinearSSSP.Decremental.step p c)))))))) ∧ ((((((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  DecrAlmostLinearSSSP.Decremental.FaultWellFormed c →
    DecrAlmostLinearSSSP.Decremental.FaultWellFormed (DecrAlmostLinearSSSP.Decremental.execute p c t)) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  @Eq.{1} Bool c.fault Bool.false →
    @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c t).halted Bool.false →
      @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c t).fault Bool.false)) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
        DecrAlmostLinearSSSP.Decremental.Instruction
        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code p.query)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
        (DecrAlmostLinearSSSP.Decremental.Instruction.loadN
          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))) →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) p.query
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
          (DecrAlmostLinearSSSP.Decremental.Instruction.load
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) p.query
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            DecrAlmostLinearSSSP.Decremental.Instruction.halt) →
        ∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (v : Nat),
          ∃ d,
            And
              (DecrAlmostLinearSSSP.Decremental.Ends p
                (have __src := DecrAlmostLinearSSSP.Decremental.resume c p.query;
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
                  (And
                    (@Eq.{1} Real (d.realReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (c.realMem v))
                    (And (@Eq.{1} (Nat → Real) d.realMem c.realMem) (@Eq.{1} (Nat → Nat) d.natMem c.natMem)))))) ∧ (∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt (DecrAlmostLinearSSSP.Decremental.Structured.program init update)
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (DecrAlmostLinearSSSP.Decremental.Structured.compile init
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) ∧ (((∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
      DecrAlmostLinearSSSP.Decremental.Instruction
      (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.Structured.program init update).code
      (DecrAlmostLinearSSSP.Decremental.Structured.codeSize init))
    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction DecrAlmostLinearSSSP.Decremental.Instruction.halt)) ∧ (∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt (DecrAlmostLinearSSSP.Decremental.Structured.program init update)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (DecrAlmostLinearSSSP.Decremental.Structured.codeSize init)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (DecrAlmostLinearSSSP.Decremental.Structured.compile update
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (DecrAlmostLinearSSSP.Decremental.Structured.codeSize init)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ ((∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
      DecrAlmostLinearSSSP.Decremental.Instruction
      (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.Structured.program init update).code
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (DecrAlmostLinearSSSP.Decremental.Structured.codeSize init)
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (DecrAlmostLinearSSSP.Decremental.Structured.codeSize update)))
    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction DecrAlmostLinearSSSP.Decremental.Instruction.halt)) ∧ ((∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd),
  DecrAlmostLinearSSSP.Decremental.Structured.CodeAt (DecrAlmostLinearSSSP.Decremental.Structured.program init update)
    (DecrAlmostLinearSSSP.Decremental.Structured.program init update).query
    (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Instruction
      (DecrAlmostLinearSSSP.Decremental.Instruction.loadN (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
        (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
      (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Instruction
        (DecrAlmostLinearSSSP.Decremental.Instruction.load (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
        (@List.cons.{0} DecrAlmostLinearSSSP.Decremental.Instruction DecrAlmostLinearSSSP.Decremental.Instruction.halt
          (@List.nil.{0} DecrAlmostLinearSSSP.Decremental.Instruction))))) ∧ (∀ (init update : DecrAlmostLinearSSSP.Decremental.Structured.Cmd) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (v : Nat),
  ∃ d,
    And
      (DecrAlmostLinearSSSP.Decremental.Ends (DecrAlmostLinearSSSP.Decremental.Structured.program init update)
        (have __src :=
          DecrAlmostLinearSSSP.Decremental.resume c
            (DecrAlmostLinearSSSP.Decremental.Structured.program init update).query;
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
            (And (@Eq.{1} (Nat → Real) d.realMem c.realMem) (@Eq.{1} (Nat → Nat) d.natMem c.natMem)))))))))) ∧ ((((∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (start : Nat) (c : DecrAlmostLinearSSSP.Decremental.Machine),
      DecrAlmostLinearSSSP.Decremental.Structured.CodeAt p start
          (DecrAlmostLinearSSSP.Decremental.Structured.compile cmd start) →
        @Eq.{1} Nat c.pc start →
          @Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data (DecrAlmostLinearSSSP.Decremental.Structured.data c)
              s →
            @Eq.{1} Bool c.halted Bool.false →
              @Eq.{1} Bool c.fault Bool.false →
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start
                        (DecrAlmostLinearSSSP.Decremental.Structured.codeSize cmd)))
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                      DecrAlmostLinearSSSP.Decremental.Instruction.halt) →
                  ∃ d,
                    And (DecrAlmostLinearSSSP.Decremental.Ends p c d)
                      (And
                        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Structured.Data
                          (DecrAlmostLinearSSSP.Decremental.Structured.data d) t)
                        (@Eq.{1} Nat d.work
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work cost)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d q : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.natural d q) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg, natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d q,
      realMem := s.realMem, natMem := s.natMem })) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d : Nat) (q : Rat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.rational d q) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@Rat.cast.{0} Real Real.instRatCast q),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem }) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.cast d a) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@Nat.cast.{0} Real Real.instNatCast (s.natReg a)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem }) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.add d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (s.realReg a) (s.realReg b)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem })))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.sub d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (s.realReg a) (s.realReg b)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem }) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.mul d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (s.realReg a) (s.realReg b)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem })) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.div d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    {
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (s.realReg a) (s.realReg b)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem }) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.nadd d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg,
      natReg :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (s.natReg a) (s.natReg b)),
      realMem := s.realMem, natMem := s.natMem }) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a b : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.nsub d a b) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg,
      natReg :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) (s.natReg a) (s.natReg b)),
      realMem := s.realMem, natMem := s.natMem })))))) ∧ (((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.load d a) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realReg d (s.realMem (s.natReg a)),
      natReg := s.natReg, realMem := s.realMem, natMem := s.natMem }) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (a d : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.store a d) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg, natReg := s.natReg,
      realMem := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem (s.natReg a) (s.realReg d),
      natMem := s.natMem })) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (d a : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.loadN d a) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg,
      natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg d (s.natMem (s.natReg a)),
      realMem := s.realMem, natMem := s.natMem }) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (a d : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Structured.storeN a d) s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    { realReg := s.realReg, natReg := s.natReg, realMem := s.realMem,
      natMem := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem (s.natReg a) (s.natReg d) }))) ∧ (((∀ (atoms : List.{0} DecrAlmostLinearSSSP.Decremental.Structured.Atom)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval
    (DecrAlmostLinearSSSP.Decremental.Structured.sequence
      (@List.map.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Atom DecrAlmostLinearSSSP.Decremental.Structured.Cmd
        DecrAlmostLinearSSSP.Decremental.Structured.Cmd.atom atoms))
    s (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Structured.Atom atoms)
    (@List.foldl.{0, 0} DecrAlmostLinearSSSP.Decremental.Structured.Data
      DecrAlmostLinearSSSP.Decremental.Structured.Atom (fun t a => a.effect t) s atoms)) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      Not (DecrAlmostLinearSSSP.Decremental.writesNat ins k) →
        @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.step p c).natReg k) (c.natReg k))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (k : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      Not (DecrAlmostLinearSSSP.Decremental.writesReal ins k) →
        @Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.step p c).realReg k) (c.realReg k)) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t k : Nat),
  (∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j t →
        ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
                (DecrAlmostLinearSSSP.Decremental.execute p c j).pc)
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
            Not (DecrAlmostLinearSSSP.Decremental.writesNat ins k)) →
    @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.execute p c t).natReg k) (c.natReg k)) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t k : Nat),
  (∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j t →
        ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
                (DecrAlmostLinearSSSP.Decremental.execute p c j).pc)
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
            Not (DecrAlmostLinearSSSP.Decremental.writesReal ins k)) →
    @Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.execute p c t).realReg k) (c.realReg k)))))) ∧ ((((∀ (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (k : Nat),
  Not (DecrAlmostLinearSSSP.Decremental.writesNat a.instruction k) → @Eq.{1} Nat ((a.effect s).natReg k) (s.natReg k)) ∧ (∀ (a : DecrAlmostLinearSSSP.Decremental.Structured.Atom) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (k : Nat),
  Not (DecrAlmostLinearSSSP.Decremental.writesReal a.instruction k) →
    @Eq.{1} Real ((a.effect s).realReg k) (s.realReg k))) ∧ ((∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost k : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame cmd k → @Eq.{1} Nat (t.natReg k) (s.natReg k)) ∧ ((∀ {cmd : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost k : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval cmd s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame cmd k → @Eq.{1} Real (t.realReg k) (s.realReg k)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Allocate.node s
    (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Allocate.nodeData s))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Exact.Allocate.nodeData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 272) (instOfNatNat (nat_lit 272))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.Allocate.nodeData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
          (And
            (DecrAlmostLinearSSSP.Decremental.Exact.Allocate.NodeImage
              (DecrAlmostLinearSSSP.Decremental.Exact.Allocate.nodeData s)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
              { count := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
                left := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
                right := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)),
                payload := @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)) })
            (And (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Exact.Allocate.nodeData s).realMem s.realMem)
              (∀ (address : Nat),
                Or
                    (@LT.lt.{0} Nat instLTNat address
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                    (@LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      address) →
                  @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.Exact.Allocate.nodeData s).natMem address)
                    (s.natMem address)))))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 272) (instOfNatNat (nat_lit 272))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 274) (instOfNatNat (nat_lit 274))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))) →
        DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.Allocate.node k)) ∧ ((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.Allocate.node k) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.Allocate.item s
    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
    (DecrAlmostLinearSSSP.Decremental.Exact.Allocate.itemData s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Exact.Allocate.itemData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 272) (instOfNatNat (nat_lit 272))))
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.Allocate.itemData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.Exact.Allocate.itemData s).natMem
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 262) (instOfNatNat (nat_lit 262)))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.Exact.Allocate.itemData s).natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 276) (instOfNatNat (nat_lit 276)))))
              (And (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Exact.Allocate.itemData s).realMem s.realMem)
                (∀ (address : Nat),
                  Or
                      (@LT.lt.{0} Nat instLTNat address
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244)))))
                      (@LE.le.{0} Nat instLENat
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 244) (instOfNatNat (nat_lit 244))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        address) →
                    @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.Exact.Allocate.itemData s).natMem address)
                      (s.natMem address)))))))))))))) := by sorry
