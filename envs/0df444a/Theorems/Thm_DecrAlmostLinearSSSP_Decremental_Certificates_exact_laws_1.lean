-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_1
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:13:40.84879+00:00
-- url     : https://prove2.me/theorems/2cfd77ff-98e2-41fa-86e9-2c12669c26e7
-- title:
--   Radix-queue semantics and scalar instruction simulation
-- statement:
--   This collection gives the universally quantified contracts for radix-queue semantics and scalar instruction simulation. All graph identifiers, queue keys, payloads, registers and addresses are finite natural indices; capacities and arithmetic registers use the scalar RAM types defined in the accompanying interface.
--
--   For a binary radix trie of height $h$ with lower key offset $l$, the multiset of queue entries has cardinality equal to the stored count, and every entry has a key in $[l,l+2^h)$. Insertion adds the supplied key-payload pair; extraction removes a minimum-key pair. The same collection contains the scalar RAM instruction-simulation contracts for shifted registers and addresses: decoded states, machine counters, branches, reads and writes agree with their source instruction semantics.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_1 : (((((((∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) (low : Nat),
  @Eq.{1} Nat
    (@Multiset.card.{0} (Prod.{0, 0} Nat Nat) (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height t low))
    (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height t)) ∧ (∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) (low key value : Nat),
  @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Multiset.{0} (Prod.{0, 0} Nat Nat))
      (@Multiset.instMembership.{0} (Prod.{0, 0} Nat Nat))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height t low) (@Prod.mk.{0, 0} Nat Nat key value) →
    And (@LE.le.{0} Nat instLENat low key)
      (@LT.lt.{0} Nat instLTNat key
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) low
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) height))))) ∧ ((∀ (height key value : Nat) (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height),
  @Eq.{1} Nat
    (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height
      (DecrAlmostLinearSSSP.Decremental.RadixQueue.insert height key value t))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height t)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) ∧ (∀ (height key value : Nat) (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) (low : Nat),
  @LT.lt.{0} Nat instLTNat key
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) height) →
    @Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height
        (DecrAlmostLinearSSSP.Decremental.RadixQueue.insert height key value t) low)
      (@Multiset.cons.{0} (Prod.{0, 0} Nat Nat)
        (@Prod.mk.{0, 0} Nat Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) low key) value)
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height t low))))) ∧ (((∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height),
  Iff
    (@Eq.{1} (Option.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height))))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.pop height t)
      (@Option.none.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)))))
    (@Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height t)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) ∧ (∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) (low : Nat),
  @Eq.{1} (Option.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height))))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.pop height t)
      (@Option.none.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)))) →
    @Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height t low)
      (@OfNat.ofNat.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (nat_lit 0)
        (@Zero.toOfNat0.{0} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (@Multiset.instZero.{0} (Prod.{0, 0} Nat Nat)))))) ∧ ((∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) (low key value : Nat)
  (next : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height),
  @Eq.{1} (Option.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height))))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.pop height t)
      (@Option.some.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)))
        (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)) key
          (@Prod.mk.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) value next))) →
    And
      (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height t low)
        (@Multiset.cons.{0} (Prod.{0, 0} Nat Nat)
          (@Prod.mk.{0, 0} Nat Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) low key) value)
          (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height next low)))
      (∀ (item : Prod.{0, 0} Nat Nat),
        @Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (Multiset.{0} (Prod.{0, 0} Nat Nat))
            (@Multiset.instMembership.{0} (Prod.{0, 0} Nat Nat))
            (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries height t low) item →
          @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) low key)
            (@Prod.fst.{0, 0} Nat Nat item))) ∧ ((∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) (key value : Nat)
  (next : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height),
  @Eq.{1} (Option.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height))))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.pop height t)
      (@Option.some.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)))
        (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)) key
          (@Prod.mk.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) value next))) →
    @Eq.{1} Nat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height next)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height t)) ∧ (∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) (key value : Nat)
  (next : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height),
  @Eq.{1} (Option.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height))))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.pop height t)
      (@Option.some.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)))
        (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)) key
          (@Prod.mk.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) value next))) →
    @LT.lt.{0} Nat instLTNat key
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) height)))))) ∧ ((((∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height),
  @LE.le.{0} Nat instLENat (@DecrAlmostLinearSSSP.Decremental.RadixQueue.popVisits height t)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) height
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) ∧ (∀ {height : Nat} (t : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height t) →
    ∃ key value next,
      @Eq.{1} (Option.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height))))
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.pop height t)
        (@Option.some.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)))
          (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height)) key
            (@Prod.mk.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height) value next))))) ∧ ((∀ {height : Nat} (left right : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie height),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) height
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie.node height left right)) →
    And
      (@Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height left)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height right))
      (@Ne.{1} Nat (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height left)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count height left))) ∧ (∀ (base : Nat), @Function.Injective.{1, 1} Nat Nat (DecrAlmostLinearSSSP.Decremental.guestAddress base)))) ∧ (((@Function.Injective.{1, 1} Nat Nat DecrAlmostLinearSSSP.Decremental.guestReg) ∧ (∀ {α : Type} (f : Nat → α) (a : Nat) (v : α),
  @Eq.{1} (Nat → α)
    (fun j =>
      @Function.update.{1, 1} Nat (fun a => α) instDecidableEqNat f (DecrAlmostLinearSSSP.Decremental.guestReg a) v
        (DecrAlmostLinearSSSP.Decremental.guestReg j))
    (@Function.update.{1, 1} Nat (fun j => α) instDecidableEqNat
      (fun j => f (DecrAlmostLinearSSSP.Decremental.guestReg j)) a v))) ∧ ((∀ {α : Type} (f : Nat → α) (base a : Nat) (v : α),
  @Eq.{1} (Nat → α)
    (fun j =>
      @Function.update.{1, 1} Nat (fun a => α) instDecidableEqNat f
        (DecrAlmostLinearSSSP.Decremental.guestAddress base a) v (DecrAlmostLinearSSSP.Decremental.guestAddress base j))
    (@Function.update.{1, 1} Nat (fun j => α) instDecidableEqNat
      (fun j => f (DecrAlmostLinearSSSP.Decremental.guestAddress base j)) a v)) ∧ ((∀ (j k : Nat),
  @LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) →
    @Ne.{1} Nat (DecrAlmostLinearSSSP.Decremental.guestReg j) k) ∧ (∀ {α : Type} (f : Nat → α) (a b : Nat) (v : α),
  @Eq.{1} α
    (@Function.update.{1, 1} Nat (fun a => α) instDecidableEqNat f (DecrAlmostLinearSSSP.Decremental.guestReg a) v
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b))
    (f
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)))))))) ∧ (((((∀ {α : Type} (f : Nat → α) (base a b : Nat) (v : α),
  @Eq.{1} α
    (@Function.update.{1, 1} Nat (fun a => α) instDecidableEqNat f
      (DecrAlmostLinearSSSP.Decremental.guestAddress base a) v
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)))
    (f
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b)))) ∧ (∀ {α : Type} (f : Nat → α) (base a b : Nat) (v : α),
  @LT.lt.{0} Nat instLTNat b base →
    @Eq.{1} α
      (@Function.update.{1, 1} Nat (fun a => α) instDecidableEqNat f
        (DecrAlmostLinearSSSP.Decremental.guestAddress base a) v b)
      (f b))) ∧ ((∀ (offset returnPC pc : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} Nat
    (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction
      (DecrAlmostLinearSSSP.Decremental.embeddedInstruction offset returnPC pc ins))
    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))) ∧ (∀ {c d : DecrAlmostLinearSSSP.Decremental.Machine},
  @Eq.{1} Nat c.pc d.pc →
    @Eq.{1} (Nat → Real) c.realReg d.realReg →
      @Eq.{1} (Nat → Nat) c.natReg d.natReg →
        @Eq.{1} (Nat → Real) c.realMem d.realMem →
          @Eq.{1} (Nat → Nat) c.natMem d.natMem →
            @Eq.{1} Bool c.halted d.halted →
              @Eq.{1} Bool c.fault d.fault →
                @Eq.{1} Nat c.work d.work → @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine c d))) ∧ (((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc work hostPC : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.decodeGuest
      { pc := hostPC, realReg := c.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) pc)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) work,
        realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work })
    (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
    { pc := pc, realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem, natMem := __src.natMem,
      halted := __src.halted, fault := __src.fault, work := work })) ∧ (∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            (DecrAlmostLinearSSSP.Decremental.Instruction.natural
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
          @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
            (DecrAlmostLinearSSSP.Decremental.decodeGuest
              (DecrAlmostLinearSSSP.Decremental.execute host c
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
            {
              pc :=
                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
              realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem, natMem := __src.natMem,
              halted := __src.halted, fault := __src.fault,
              work :=
                @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (DecrAlmostLinearSSSP.Decremental.decodeGuest c).work
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.step p c)
        (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
          {
            pc :=
              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
            realReg := c.realReg, natReg := c.natReg, realMem := c.realMem, natMem := c.natMem, halted := c.halted,
            fault := c.fault,
            work :=
              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })) ∧ ((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc work : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.decodeGuest
      { pc := pc, realReg := c.realReg, natReg := c.natReg, realMem := c.realMem, natMem := c.natMem,
        halted := c.halted, fault := c.fault, work := work })
    (DecrAlmostLinearSSSP.Decremental.decodeGuest c)) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
        (DecrAlmostLinearSSSP.Decremental.decodeGuest (DecrAlmostLinearSSSP.Decremental.step p c))
        (DecrAlmostLinearSSSP.Decremental.decodeGuest (DecrAlmostLinearSSSP.Decremental.instructionEffect ins c))))))) ∧ ((((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (a : Nat) (value : Real),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.decodeGuest
      { pc := c.pc,
        realReg :=
          @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat c.realReg
            (DecrAlmostLinearSSSP.Decremental.guestReg a) value,
        natReg := c.natReg, realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault,
        work := c.work })
    (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
    { pc := __src.pc,
      realReg :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat
          (DecrAlmostLinearSSSP.Decremental.decodeGuest c).realReg a value,
      natReg := __src.natReg, realMem := __src.realMem, natMem := __src.natMem, halted := __src.halted,
      fault := __src.fault, work := __src.work })) ∧ (∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (a value : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.decodeGuest
      { pc := c.pc, realReg := c.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
            (DecrAlmostLinearSSSP.Decremental.guestReg a) value,
        realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work })
    (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
    { pc := __src.pc, realReg := __src.realReg,
      natReg :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (DecrAlmostLinearSSSP.Decremental.decodeGuest c).natReg a value,
      realMem := __src.realMem, natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
      work := __src.work }))) ∧ ((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (a : Nat) (value : Real),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.decodeGuest
      { pc := c.pc, realReg := c.realReg, natReg := c.natReg,
        realMem :=
          @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat c.realMem
            (DecrAlmostLinearSSSP.Decremental.guestAddress
              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) a)
            value,
        natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work })
    (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
    { pc := __src.pc, realReg := __src.realReg, natReg := __src.natReg,
      realMem :=
        @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat
          (DecrAlmostLinearSSSP.Decremental.decodeGuest c).realMem a value,
      natMem := __src.natMem, halted := __src.halted, fault := __src.fault, work := __src.work })) ∧ ((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (a value : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.decodeGuest
      { pc := c.pc, realReg := c.realReg, natReg := c.natReg, realMem := c.realMem,
        natMem :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natMem
            (DecrAlmostLinearSSSP.Decremental.guestAddress
              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) a)
            value,
        halted := c.halted, fault := c.fault, work := c.work })
    (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
    { pc := __src.pc, realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem,
      natMem :=
        @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (DecrAlmostLinearSSSP.Decremental.decodeGuest c).natMem a value,
      halted := __src.halted, fault := __src.fault, work := __src.work })) ∧ (∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (a : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.decodeGuest
      { pc := c.pc, realReg := c.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) a,
        realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work })
    (DecrAlmostLinearSSSP.Decremental.decodeGuest c))))) ∧ (((∀ (ins translated : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.scalarTranslation ins)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction translated) →
    ∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
      @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
        (DecrAlmostLinearSSSP.Decremental.decodeGuest (DecrAlmostLinearSSSP.Decremental.instructionEffect translated c))
        (DecrAlmostLinearSSSP.Decremental.instructionEffect ins (DecrAlmostLinearSSSP.Decremental.decodeGuest c))) ∧ (∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (d a : Nat),
  @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
      (DecrAlmostLinearSSSP.Decremental.guestAddress
        (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (c.natReg (DecrAlmostLinearSSSP.Decremental.guestReg a))) →
    @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
      (DecrAlmostLinearSSSP.Decremental.decodeGuest
        (DecrAlmostLinearSSSP.Decremental.instructionEffect
          (DecrAlmostLinearSSSP.Decremental.Instruction.load (DecrAlmostLinearSSSP.Decremental.guestReg d)
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          c))
      (DecrAlmostLinearSSSP.Decremental.instructionEffect (DecrAlmostLinearSSSP.Decremental.Instruction.load d a)
        (DecrAlmostLinearSSSP.Decremental.decodeGuest c)))) ∧ ((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (d a : Nat),
  @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
      (DecrAlmostLinearSSSP.Decremental.guestAddress
        (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (c.natReg (DecrAlmostLinearSSSP.Decremental.guestReg a))) →
    @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
      (DecrAlmostLinearSSSP.Decremental.decodeGuest
        (DecrAlmostLinearSSSP.Decremental.instructionEffect
          (DecrAlmostLinearSSSP.Decremental.Instruction.loadN (DecrAlmostLinearSSSP.Decremental.guestReg d)
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          c))
      (DecrAlmostLinearSSSP.Decremental.instructionEffect (DecrAlmostLinearSSSP.Decremental.Instruction.loadN d a)
        (DecrAlmostLinearSSSP.Decremental.decodeGuest c))) ∧ ((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (a d : Nat),
  @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
      (DecrAlmostLinearSSSP.Decremental.guestAddress
        (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (c.natReg (DecrAlmostLinearSSSP.Decremental.guestReg a))) →
    @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
      (DecrAlmostLinearSSSP.Decremental.decodeGuest
        (DecrAlmostLinearSSSP.Decremental.instructionEffect
          (DecrAlmostLinearSSSP.Decremental.Instruction.store
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) (DecrAlmostLinearSSSP.Decremental.guestReg d))
          c))
      (DecrAlmostLinearSSSP.Decremental.instructionEffect (DecrAlmostLinearSSSP.Decremental.Instruction.store a d)
        (DecrAlmostLinearSSSP.Decremental.decodeGuest c))) ∧ (∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (a d : Nat),
  @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
      (DecrAlmostLinearSSSP.Decremental.guestAddress
        (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (c.natReg (DecrAlmostLinearSSSP.Decremental.guestReg a))) →
    @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
      (DecrAlmostLinearSSSP.Decremental.decodeGuest
        (DecrAlmostLinearSSSP.Decremental.instructionEffect
          (DecrAlmostLinearSSSP.Decremental.Instruction.storeN
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) (DecrAlmostLinearSSSP.Decremental.guestReg d))
          c))
      (DecrAlmostLinearSSSP.Decremental.instructionEffect (DecrAlmostLinearSSSP.Decremental.Instruction.storeN a d)
        (DecrAlmostLinearSSSP.Decremental.decodeGuest c))))))))) ∧ ((((((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (a b : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.execute p c (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b))
    (DecrAlmostLinearSSSP.Decremental.execute p (DecrAlmostLinearSSSP.Decremental.execute p c a) b)) ∧ (∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (target : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
          (DecrAlmostLinearSSSP.Decremental.Instruction.jump target)) →
      @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
        (DecrAlmostLinearSSSP.Decremental.execute host c (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        { pc := target, realReg := c.realReg, natReg := c.natReg, realMem := c.realMem, natMem := c.natMem,
          halted := c.halted, fault := c.fault,
          work :=
            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })) ∧ ((∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (ins translated : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.scalarTranslation ins)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction translated) →
    @Eq.{1} Bool c.halted Bool.false →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction translated) →
        And
          (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
            (DecrAlmostLinearSSSP.Decremental.decodeGuest
              (DecrAlmostLinearSSSP.Decremental.execute host c
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (DecrAlmostLinearSSSP.Decremental.instructionEffect ins (DecrAlmostLinearSSSP.Decremental.decodeGuest c)))
          (And
            (@Eq.{1} Nat
              (DecrAlmostLinearSSSP.Decremental.execute host c
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).pc
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (And
              (@Eq.{1} Bool
                (DecrAlmostLinearSSSP.Decremental.execute host c
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).halted
                Bool.false)
              (@Eq.{1} Nat
                (DecrAlmostLinearSSSP.Decremental.execute host c
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).work
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) ∧ (∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (a : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
              (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
              (DecrAlmostLinearSSSP.Decremental.guestReg a) (DecrAlmostLinearSSSP.Decremental.guestReg a))) →
        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) →
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
            ∃ d,
              And
                (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                  (DecrAlmostLinearSSSP.Decremental.execute host c
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  d)
                (And
                  (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                    (DecrAlmostLinearSSSP.Decremental.decodeGuest c))
                  (And
                    (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
                      (DecrAlmostLinearSSSP.Decremental.guestAddress
                        (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                        (d.natReg (DecrAlmostLinearSSSP.Decremental.guestReg a))))
                    (And
                      (@Eq.{1} Nat d.pc
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                      (And (@Eq.{1} Bool d.halted Bool.false)
                        (And
                          (@Eq.{1} Nat d.work
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          (And
                            (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                            (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))))) ∧ (((∀ (offset returnPC start : Nat) (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} Nat
    (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction
      (DecrAlmostLinearSSSP.Decremental.embeddedCodeAux offset returnPC start code))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
      (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction code))) ∧ (∀ (offset returnPC : Nat) (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} Nat
    (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction
      (DecrAlmostLinearSSSP.Decremental.embeddedCode offset returnPC code))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
      (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction code)))) ∧ ((∀ (offset returnPC start : Nat) (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc slot : Nat)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @LT.lt.{0} Nat instLTNat slot (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (DecrAlmostLinearSSSP.Decremental.embeddedCodeAux offset returnPC start code)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) pc)
            slot))
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (DecrAlmostLinearSSSP.Decremental.embeddedInstruction offset returnPC
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) start pc) ins)
          slot)) ∧ ((∀ (offset returnPC : Nat) (code : List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) (pc slot : Nat)
  (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @LT.lt.{0} Nat instLTNat slot (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) code pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (DecrAlmostLinearSSSP.Decremental.embeddedCode offset returnPC code)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) pc)
            slot))
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (DecrAlmostLinearSSSP.Decremental.embeddedInstruction offset returnPC pc ins) slot)) ∧ (∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            (DecrAlmostLinearSSSP.Decremental.Instruction.natural
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
          @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
            (DecrAlmostLinearSSSP.Decremental.execute host c
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (DecrAlmostLinearSSSP.Decremental.headerState c pc)))))) ∧ ((((∀ (ins translated : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.scalarTranslation ins)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction translated) →
    ∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.instructionEffect translated c).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.instructionEffect translated c).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.instructionEffect translated c).fault c.fault))) ∧ (∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc offset : Nat)
  (ins translated : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.scalarTranslation ins)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction translated) →
    @Eq.{1} Bool c.halted Bool.false →
      @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.natural
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                  DecrAlmostLinearSSSP.Decremental.Instruction
                  (fun as i =>
                    @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                  (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction translated) →
              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                    (DecrAlmostLinearSSSP.Decremental.Instruction.jump
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) →
                ∃ d,
                  And
                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                      (DecrAlmostLinearSSSP.Decremental.execute host c
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      d)
                    (And
                      (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                        (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                          (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
                          {
                            pc :=
                              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                            realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem,
                            natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
                            work :=
                              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (DecrAlmostLinearSSSP.Decremental.decodeGuest c).work
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })))
                      (And
                        (@Eq.{1} Nat d.pc
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                        (And
                          (@Eq.{1} Nat d.work
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                          (And (@Eq.{1} Bool d.halted Bool.false)
                            (And
                              (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                              (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))) ∧ ((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.decodeGuest
      { pc := c.pc, realReg := c.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) pc,
        realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work })
    (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
    { pc := pc, realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem, natMem := __src.natMem,
      halted := __src.halted, fault := __src.fault, work := __src.work })) ∧ ((∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.decodeGuest
      { pc := c.pc, realReg := c.realReg,
        natReg :=
          @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
        realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault, work := c.work })
    (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
    { pc := __src.pc, realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem,
      natMem := __src.natMem, halted := Bool.true, fault := __src.fault, work := __src.work })) ∧ (∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (reg value target : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
          (DecrAlmostLinearSSSP.Decremental.Instruction.natural reg value)) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            (DecrAlmostLinearSSSP.Decremental.Instruction.jump target)) →
        @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
          (DecrAlmostLinearSSSP.Decremental.execute host c
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          { pc := target, realReg := c.realReg,
            natReg := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat c.natReg reg value,
            realMem := c.realMem, natMem := c.natMem, halted := c.halted, fault := c.fault,
            work :=
              @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) })))) ∧ (((∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (pc offset target : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            (DecrAlmostLinearSSSP.Decremental.Instruction.natural
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                (DecrAlmostLinearSSSP.Decremental.Instruction.natural
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) target)) →
            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                  DecrAlmostLinearSSSP.Decremental.Instruction
                  (fun as i =>
                    @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                  (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                  (DecrAlmostLinearSSSP.Decremental.Instruction.jump
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) target)))) →
              ∃ d,
                And
                  (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                    (DecrAlmostLinearSSSP.Decremental.execute host c
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    d)
                  (And
                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                      (DecrAlmostLinearSSSP.Decremental.instructionEffect
                        (DecrAlmostLinearSSSP.Decremental.Instruction.jump target)
                        (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
                        {
                          pc :=
                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                          realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem,
                          natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
                          work :=
                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.decodeGuest c).work
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })))
                    (And
                      (@Eq.{1} Nat d.pc
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) target)))
                      (And
                        (@Eq.{1} Nat d.work
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                        (And (@Eq.{1} Bool d.halted Bool.false)
                          (And
                            (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                            (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))) ∧ (∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc returnPC : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            (DecrAlmostLinearSSSP.Decremental.Instruction.natural
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                (DecrAlmostLinearSSSP.Decremental.Instruction.natural
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                  DecrAlmostLinearSSSP.Decremental.Instruction
                  (fun as i =>
                    @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                  (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                  (DecrAlmostLinearSSSP.Decremental.Instruction.jump returnPC)) →
              ∃ d,
                And
                  (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                    (DecrAlmostLinearSSSP.Decremental.execute host c
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    d)
                  (And
                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                      (DecrAlmostLinearSSSP.Decremental.instructionEffect
                        DecrAlmostLinearSSSP.Decremental.Instruction.halt
                        (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
                        {
                          pc :=
                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                          realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem,
                          natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
                          work :=
                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.decodeGuest c).work
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })))
                    (And (@Eq.{1} Nat d.pc returnPC)
                      (And
                        (@Eq.{1} Nat d.work
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                        (And (@Eq.{1} Bool d.halted Bool.false)
                          (And
                            (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                            (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))) ∧ ((∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (natural : Bool)
  (a b target : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
          DecrAlmostLinearSSSP.Decremental.Instruction
          (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
          (DecrAlmostLinearSSSP.Decremental.branchInstruction natural (DecrAlmostLinearSSSP.Decremental.guestReg a)
            (DecrAlmostLinearSSSP.Decremental.guestReg b) target)) →
      @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
        (DecrAlmostLinearSSSP.Decremental.execute host c (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        {
          pc :=
            @ite.{1} Nat
              (DecrAlmostLinearSSSP.Decremental.branchTest natural (DecrAlmostLinearSSSP.Decremental.decodeGuest c) a b)
              (Classical.propDecidable
                (DecrAlmostLinearSSSP.Decremental.branchTest natural (DecrAlmostLinearSSSP.Decremental.decodeGuest c) a
                  b))
              target
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))),
          realReg := c.realReg, natReg := c.natReg, realMem := c.realMem, natMem := c.natMem, halted := c.halted,
          fault := c.fault,
          work :=
            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) }) ∧ ((∀ (natural : Bool) (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc a b : Nat),
  @Eq.{1} Prop
    (DecrAlmostLinearSSSP.Decremental.branchTest natural
      (DecrAlmostLinearSSSP.Decremental.decodeGuest (DecrAlmostLinearSSSP.Decremental.headerState c pc)) a b)
    (DecrAlmostLinearSSSP.Decremental.branchTest natural (DecrAlmostLinearSSSP.Decremental.decodeGuest c) a b)) ∧ (∀ (natural : Bool) (c : DecrAlmostLinearSSSP.Decremental.Machine) (a b target : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.instructionEffect
      (DecrAlmostLinearSSSP.Decremental.branchInstruction natural a b target) c)
    (@ite.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.branchTest natural c a b)
      (Classical.propDecidable (DecrAlmostLinearSSSP.Decremental.branchTest natural c a b))
      { pc := target, realReg := c.realReg, natReg := c.natReg, realMem := c.realMem, natMem := c.natMem,
        halted := c.halted, fault := c.fault, work := c.work }
      c))))))) ∧ (((((∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (pc offset target : Nat) (natural : Bool) (a b : Nat),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
          (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
            DecrAlmostLinearSSSP.Decremental.Instruction
            (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
            (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
            (DecrAlmostLinearSSSP.Decremental.Instruction.natural
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                (DecrAlmostLinearSSSP.Decremental.branchInstruction natural
                  (DecrAlmostLinearSSSP.Decremental.guestReg a) (DecrAlmostLinearSSSP.Decremental.guestReg b)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                    (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))) →
            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                  DecrAlmostLinearSSSP.Decremental.Instruction
                  (fun as i =>
                    @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                  (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                  (DecrAlmostLinearSSSP.Decremental.Instruction.jump
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) →
              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                      (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                    (DecrAlmostLinearSSSP.Decremental.Instruction.natural
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) target)) →
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                      (DecrAlmostLinearSSSP.Decremental.Instruction.jump
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) target)))) →
                  ∃ steps d,
                    And (@LE.le.{0} Nat instLENat steps (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))))
                      (And
                        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                          (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                        (And
                          (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                            (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                            (DecrAlmostLinearSSSP.Decremental.instructionEffect
                              (DecrAlmostLinearSSSP.Decremental.branchInstruction natural a b target)
                              (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
                              {
                                pc :=
                                  @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                                realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem,
                                natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
                                work :=
                                  @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (DecrAlmostLinearSSSP.Decremental.decodeGuest c).work
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })))
                          (And
                            (@Eq.{1} Nat d.pc
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                                  (DecrAlmostLinearSSSP.Decremental.decodeGuest d).pc)))
                            (And
                              (@Eq.{1} Nat d.work
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work steps))
                              (And (@Eq.{1} Bool d.halted Bool.false)
                                (And
                                  (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                    (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                  (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))) ∧ (∀ (ins translated : DecrAlmostLinearSSSP.Decremental.Instruction) (a : Nat),
  @Eq.{1} (Option.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat))
      (DecrAlmostLinearSSSP.Decremental.memoryTranslation ins)
      (@Option.some.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat)
        (@Prod.mk.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat translated a)) →
    ∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
      @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (DecrAlmostLinearSSSP.Decremental.guestAddress
            (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            (c.natReg (DecrAlmostLinearSSSP.Decremental.guestReg a))) →
        @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
          (DecrAlmostLinearSSSP.Decremental.decodeGuest
            (DecrAlmostLinearSSSP.Decremental.instructionEffect translated c))
          (DecrAlmostLinearSSSP.Decremental.instructionEffect ins (DecrAlmostLinearSSSP.Decremental.decodeGuest c)))) ∧ ((∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (ins translated : DecrAlmostLinearSSSP.Decremental.Instruction) (a : Nat),
  @Eq.{1} (Option.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat))
      (DecrAlmostLinearSSSP.Decremental.memoryTranslation ins)
      (@Option.some.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat)
        (@Prod.mk.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat translated a)) →
    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
        (DecrAlmostLinearSSSP.Decremental.guestAddress
          (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (c.natReg (DecrAlmostLinearSSSP.Decremental.guestReg a))) →
      @Eq.{1} Bool c.halted Bool.false →
        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction translated) →
          And
            (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
              (DecrAlmostLinearSSSP.Decremental.decodeGuest
                (DecrAlmostLinearSSSP.Decremental.execute host c
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (DecrAlmostLinearSSSP.Decremental.instructionEffect ins (DecrAlmostLinearSSSP.Decremental.decodeGuest c)))
            (And
              (@Eq.{1} Nat
                (DecrAlmostLinearSSSP.Decremental.execute host c
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).pc
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (And
                (@Eq.{1} Bool
                  (DecrAlmostLinearSSSP.Decremental.execute host c
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).halted
                  Bool.false)
                (And
                  (@Eq.{1} Nat
                    (DecrAlmostLinearSSSP.Decremental.execute host c
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).work
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  (And
                    (@Eq.{1} Nat
                      ((DecrAlmostLinearSSSP.Decremental.execute host c
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).natReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                      (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                    (@Eq.{1} Nat
                      ((DecrAlmostLinearSSSP.Decremental.execute host c
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))).natReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                      (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))) ∧ (∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (pc offset : Nat)
  (ins translated : DecrAlmostLinearSSSP.Decremental.Instruction) (a : Nat),
  @Eq.{1} (Option.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat))
      (DecrAlmostLinearSSSP.Decremental.memoryTranslation ins)
      (@Option.some.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat)
        (@Prod.mk.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat translated a)) →
    @Eq.{1} Bool c.halted Bool.false →
      @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
            (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
              DecrAlmostLinearSSSP.Decremental.Instruction
              (fun as i =>
                @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
              (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code c.pc)
            (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
              (DecrAlmostLinearSSSP.Decremental.Instruction.natural
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
          @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                  DecrAlmostLinearSSSP.Decremental.Instruction
                  (fun as i =>
                    @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                  (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                  (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                    (DecrAlmostLinearSSSP.Decremental.guestReg a) (DecrAlmostLinearSSSP.Decremental.guestReg a))) →
              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                    (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) →
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                      (DecrAlmostLinearSSSP.Decremental.Instruction.nadd
                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) →
                  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                        DecrAlmostLinearSSSP.Decremental.Instruction
                        (fun as i =>
                          @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                          (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction translated) →
                    @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                          DecrAlmostLinearSSSP.Decremental.Instruction
                          (fun as i =>
                            @LT.lt.{0} Nat instLTNat i
                              (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc
                            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
                          (DecrAlmostLinearSSSP.Decremental.Instruction.jump
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) →
                      ∃ d,
                        And
                          (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                            (DecrAlmostLinearSSSP.Decremental.execute host c
                              (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                            d)
                          (And
                            (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                              (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                              (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                                (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
                                {
                                  pc :=
                                    @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                                  realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem,
                                  natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
                                  work :=
                                    @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (DecrAlmostLinearSSSP.Decremental.decodeGuest c).work
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })))
                            (And
                              (@Eq.{1} Nat d.pc
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                              (And
                                (@Eq.{1} Nat d.work
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
                                (And (@Eq.{1} Bool d.halted Bool.false)
                                  (And
                                    (@Eq.{1} Nat
                                      (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                      (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                    (@Eq.{1} Nat
                                      (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))))))) ∧ (((∀ (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (DecrAlmostLinearSSSP.Decremental.scalarTranslation ins)
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction tr) →
    ∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
      And (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.instructionEffect ins c).pc c.pc)
        (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.instructionEffect ins c).halted c.halted)) ∧ (∀ (ins tr : DecrAlmostLinearSSSP.Decremental.Instruction) (a : Nat),
  @Eq.{1} (Option.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat))
      (DecrAlmostLinearSSSP.Decremental.memoryTranslation ins)
      (@Option.some.{0} (Prod.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat)
        (@Prod.mk.{0, 0} DecrAlmostLinearSSSP.Decremental.Instruction Nat tr a)) →
    ∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
      And (@Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.instructionEffect ins c).pc c.pc)
        (@Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.instructionEffect ins c).halted c.halted))) ∧ ((∀ (offset returnPC pc : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  And
    (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
        DecrAlmostLinearSSSP.Decremental.Instruction
        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (DecrAlmostLinearSSSP.Decremental.embeddedInstruction offset returnPC pc ins)
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
        (DecrAlmostLinearSSSP.Decremental.Instruction.natural
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
    (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
      (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
        DecrAlmostLinearSSSP.Decremental.Instruction
        (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
        (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
        (DecrAlmostLinearSSSP.Decremental.embeddedInstruction offset returnPC pc ins)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction
        (DecrAlmostLinearSSSP.Decremental.Instruction.nadd (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ ((∀ (host : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine)
  (pc offset returnPC : Nat) (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.decodeGuest c).halted Bool.false →
        @Eq.{1} Nat c.pc
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) pc)) →
          (∀ (slot : Nat),
              @LT.lt.{0} Nat instLTNat slot (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) →
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) host.code
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.pc slot))
                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                    DecrAlmostLinearSSSP.Decremental.Instruction
                    (fun as i =>
                      @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (DecrAlmostLinearSSSP.Decremental.embeddedInstruction offset returnPC pc ins) slot)) →
            ∃ steps d,
              And (@LE.le.{0} Nat instLENat steps (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                (And
                  (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                    (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                  (And
                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                      (DecrAlmostLinearSSSP.Decremental.instructionEffect ins
                        (have __src := DecrAlmostLinearSSSP.Decremental.decodeGuest c;
                        {
                          pc :=
                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) pc
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))),
                          realReg := __src.realReg, natReg := __src.natReg, realMem := __src.realMem,
                          natMem := __src.natMem, halted := __src.halted, fault := __src.fault,
                          work :=
                            @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (DecrAlmostLinearSSSP.Decremental.decodeGuest c).work
                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) })))
                    (And
                      (@Eq.{1} Nat d.pc
                        (DecrAlmostLinearSSSP.Decremental.embeddedDestination offset returnPC
                          (DecrAlmostLinearSSSP.Decremental.decodeGuest d)))
                      (And
                        (@Eq.{1} Nat d.work
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work steps))
                        (And (@Eq.{1} Bool d.halted Bool.false)
                          (And
                            (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                            (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))) ∧ (∀ (host guest : DecrAlmostLinearSSSP.Decremental.Program) (offset returnPC : Nat),
  DecrAlmostLinearSSSP.Decremental.EmbedsCode host guest offset returnPC →
    ∀ (c : DecrAlmostLinearSSSP.Decremental.Machine),
      @Eq.{1} Bool c.halted Bool.false →
        @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.decodeGuest c).halted Bool.false →
            @Eq.{1} Nat c.pc
                (DecrAlmostLinearSSSP.Decremental.embeddedDestination offset returnPC
                  (DecrAlmostLinearSSSP.Decremental.decodeGuest c)) →
              ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction),
                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                      DecrAlmostLinearSSSP.Decremental.Instruction
                      (fun as i =>
                        @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) guest.code
                      (DecrAlmostLinearSSSP.Decremental.decodeGuest c).pc)
                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins) →
                  ∃ steps d,
                    And (@LE.le.{0} Nat instLENat steps (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
                      (And
                        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                          (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                        (And
                          (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                            (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                            (DecrAlmostLinearSSSP.Decremental.step guest
                              (DecrAlmostLinearSSSP.Decremental.decodeGuest c)))
                          (And
                            (@Eq.{1} Nat d.pc
                              (DecrAlmostLinearSSSP.Decremental.embeddedDestination offset returnPC
                                (DecrAlmostLinearSSSP.Decremental.decodeGuest d)))
                            (And
                              (@Eq.{1} Nat d.work
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work steps))
                              (And (@Eq.{1} Bool d.halted Bool.false)
                                (And
                                  (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                    (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                                  (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                    (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))))))) ∧ ((((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Bool c.halted Bool.true →
    ∀ (t : Nat), @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.execute p c t) c) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
    (DecrAlmostLinearSSSP.Decremental.execute p c
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (DecrAlmostLinearSSSP.Decremental.execute p (DecrAlmostLinearSSSP.Decremental.step p c) t))) ∧ ((∀ (host guest : DecrAlmostLinearSSSP.Decremental.Program) (offset returnPC : Nat),
  DecrAlmostLinearSSSP.Decremental.EmbedsCode host guest offset returnPC →
    ∀ (t : Nat) (c : DecrAlmostLinearSSSP.Decremental.Machine),
      @Eq.{1} Bool c.halted Bool.false →
        @Eq.{1} Nat (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          @Eq.{1} Nat c.pc
              (DecrAlmostLinearSSSP.Decremental.embeddedDestination offset returnPC
                (DecrAlmostLinearSSSP.Decremental.decodeGuest c)) →
            (∀ (j : Nat),
                @LT.lt.{0} Nat instLTNat j t →
                  @Eq.{1} Bool
                      (DecrAlmostLinearSSSP.Decremental.execute guest (DecrAlmostLinearSSSP.Decremental.decodeGuest c)
                          j).halted
                      Bool.false →
                    ∃ ins,
                      @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
                        (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                          DecrAlmostLinearSSSP.Decremental.Instruction
                          (fun as i =>
                            @LT.lt.{0} Nat instLTNat i
                              (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                          (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) guest.code
                          (DecrAlmostLinearSSSP.Decremental.execute guest
                              (DecrAlmostLinearSSSP.Decremental.decodeGuest c) j).pc)
                        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins)) →
              ∃ steps d,
                And
                  (@LE.le.{0} Nat instLENat steps
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))) t))
                  (And
                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                      (DecrAlmostLinearSSSP.Decremental.execute host c steps) d)
                    (And
                      (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.decodeGuest d)
                        (DecrAlmostLinearSSSP.Decremental.execute guest (DecrAlmostLinearSSSP.Decremental.decodeGuest c)
                          t))
                      (And
                        (@Eq.{1} Nat d.pc
                          (DecrAlmostLinearSSSP.Decremental.embeddedDestination offset returnPC
                            (DecrAlmostLinearSSSP.Decremental.decodeGuest d)))
                        (And
                          (@Eq.{1} Nat d.work
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work steps))
                          (And (@Eq.{1} Bool d.halted Bool.false)
                            (And
                              (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
                              (@Eq.{1} Nat (d.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                (c.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Bool c.fault Bool.true → @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.step p c).fault Bool.true) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Bool c.fault Bool.true →
    ∀ (t : Nat), @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c t).fault Bool.true)))) ∧ (((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t j : Nat),
  @LE.le.{0} Nat instLENat j t →
    @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c t).fault Bool.false →
      @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c j).fault Bool.false) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (t : Nat),
  @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c t).fault Bool.false →
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j t →
        @Eq.{1} Bool (DecrAlmostLinearSSSP.Decremental.execute p c j).halted Bool.false →
          ∃ ins,
            @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Instruction)
              (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Instruction) Nat
                DecrAlmostLinearSSSP.Decremental.Instruction
                (fun as i =>
                  @LT.lt.{0} Nat instLTNat i (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Instruction as))
                (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Instruction) p.code
                (DecrAlmostLinearSSSP.Decremental.execute p c j).pc)
              (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Instruction ins))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Bool c.halted Bool.false →
    @Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.step p c).work
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @Eq.{1} Bool c.halted Bool.true →
    @Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine (DecrAlmostLinearSSSP.Decremental.step p c) c) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine),
  @LE.le.{0} Nat instLENat c.work (DecrAlmostLinearSSSP.Decremental.step p c).work)))))))) := by sorry
