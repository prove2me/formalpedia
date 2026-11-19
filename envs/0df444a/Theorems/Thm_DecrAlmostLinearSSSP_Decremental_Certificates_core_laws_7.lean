-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_7
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T17:33:27.988729+00:00
-- url     : https://prove2.me/theorems/d825f18c-b072-4167-bfc5-49b4115916a5
-- title:
--   Complete normalized-core memory initialization
-- statement:
--   Let the graph, labels, caches, cut states and scalar RAM machines be the objects of the normalized decremental SSSP implementation interface. Each component below is universally quantified over its own parameters and representation hypotheses.
--
--   Initialization over nonsource return vertices establishes the complete geometry, gradient, pending queue and public-array images of the normalized core. Source reads, return writes and initialization controls preserve the remaining records and register banks. Every initialization pass has its stated charged work bound.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_7 : (((((((∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
        (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 662) (instOfNatNat (nat_lit 662))) k))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
      DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.nonsourceCode k) ∧ (∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))))
        (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) k))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
      DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.nonsourceCode k)) ∧ ((∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
        (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 662) (instOfNatNat (nat_lit 662))) k))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.body k) ∧ (∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))))
        (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) k))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.body k))) ∧ (((@Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.code)
  Bool.true) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.advanceCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.advanced s))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.advanced s).natReg
        (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))))
    (@Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.advanced s).natReg
        (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))))) ∧ ((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.advanceCode) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
        DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.advanceCode k))))) ∧ ((((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
    DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.advanceCode k) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B j : Nat),
  @LE.le.{0} Nat instLENat j B → DecrAlmostLinearSSSP.Decremental.CoreMemory.Protected b B j)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B j : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreMemory.Protected b B
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B j : Nat),
  @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) j →
    DecrAlmostLinearSSSP.Decremental.CoreMemory.Protected b B j))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B s s) ∧ (∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B : Nat} {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B s t →
    DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B t u →
      DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B s u)) ∧ ((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B : Nat} {e : DecrAlmostLinearSSSP.Decremental.Edge b}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreMemory.EdgeFrame b B e s t →
    DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B s t) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (e d : DecrAlmostLinearSSSP.Decremental.Edge b)
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreMemory.EdgeFrame b B e s t →
    @Ne.{1} (DecrAlmostLinearSSSP.Decremental.Edge b) d e →
      DecrAlmostLinearSSSP.Decremental.CoreRecord.Initialized b B d s →
        DecrAlmostLinearSSSP.Decremental.CoreRecord.Initialized b B d t) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B s s)))))) ∧ (((((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B : Nat} {s t u : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B s t →
    DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B t u →
      DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B s u) ∧ (∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B : Nat} {v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnEdgeFrame b B v s t →
    DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B s t)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnEdgeFrame b B v s t →
      ∀ (u : Fin b.input.n),
        @Ne.{1} (Fin b.input.n) u
            (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v) →
          And (@Eq.{1} Nat (t.natMem (@Fin.val b.input.n u)) (s.natMem (@Fin.val b.input.n u)))
            (@Eq.{1} Real (t.realMem (@Fin.val b.input.n u)) (s.realMem (@Fin.val b.input.n u)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
  (d : DecrAlmostLinearSSSP.Decremental.Edge b) (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnEdgeFrame b B v s t →
      @Ne.{1} (DecrAlmostLinearSSSP.Decremental.Edge b) d
          (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v) →
        DecrAlmostLinearSSSP.Decremental.CoreRecord.Initialized b B d s →
          DecrAlmostLinearSSSP.Decremental.CoreRecord.Initialized b B d t))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (e : DecrAlmostLinearSSSP.Decremental.Edge b) (v : Fin b.input.n)
  (g : Real),
  @Eq.{1} Real
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) g
      (DecrAlmostLinearSSSP.Decremental.initialContribution b e v))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) g
        (@ite.{1} Real (@Eq.{1} (Fin b.input.n) v (DecrAlmostLinearSSSP.Decremental.tail b e))
          (instDecidableEqFin b.input.n v (DecrAlmostLinearSSSP.Decremental.tail b e))
          (DecrAlmostLinearSSSP.Decremental.capacity b (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
            (DecrAlmostLinearSSSP.Decremental.initialLabel b) e)
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
      (@ite.{1} Real (@Eq.{1} (Fin b.input.n) v (DecrAlmostLinearSSSP.Decremental.head b e))
        (instDecidableEqFin b.input.n v (DecrAlmostLinearSSSP.Decremental.head b e))
        (DecrAlmostLinearSSSP.Decremental.capacity b (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
          (DecrAlmostLinearSSSP.Decremental.initialLabel b) e)
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @Eq.{1} (Fin b.input.n → Real)
    (DecrAlmostLinearSSSP.Decremental.initialGradientThrough b
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
      (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
        (@Pi.instZero.{0, 0} (Fin b.input.n) (fun v => Real) fun i => Real.instZero))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (t : Nat)
  (ht : @LT.lt.{0} Nat instLTNat t (DecrAlmostLinearSSSP.Decremental.logicalCount b)),
  have e :=
    @DFunLike.coe.{1, 1, 1}
      (Equiv.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)) (DecrAlmostLinearSSSP.Decremental.Edge b))
      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)) (fun x => DecrAlmostLinearSSSP.Decremental.Edge b)
      (@EquivLike.toFunLike.{1, 1, 1}
        (Equiv.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)) (DecrAlmostLinearSSSP.Decremental.Edge b))
        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)) (DecrAlmostLinearSSSP.Decremental.Edge b)
        (@Equiv.instEquivLike.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
          (DecrAlmostLinearSSSP.Decremental.Edge b)))
      (@Equiv.symm.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)) (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
      (@Fin.mk (DecrAlmostLinearSSSP.Decremental.logicalCount b) t ht);
  @Eq.{1} (Fin b.input.n → Real)
    (DecrAlmostLinearSSSP.Decremental.initialGradientThrough b
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    fun v =>
    @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (DecrAlmostLinearSSSP.Decremental.initialGradientThrough b t v)
        (@ite.{1} Real (@Eq.{1} (Fin b.input.n) v (DecrAlmostLinearSSSP.Decremental.tail b e))
          (instDecidableEqFin b.input.n v (DecrAlmostLinearSSSP.Decremental.tail b e))
          (DecrAlmostLinearSSSP.Decremental.capacity b (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
            (DecrAlmostLinearSSSP.Decremental.initialLabel b) e)
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
      (@ite.{1} Real (@Eq.{1} (Fin b.input.n) v (DecrAlmostLinearSSSP.Decremental.head b e))
        (instDecidableEqFin b.input.n v (DecrAlmostLinearSSSP.Decremental.head b e))
        (DecrAlmostLinearSSSP.Decremental.capacity b (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
          (DecrAlmostLinearSSSP.Decremental.initialLabel b) e)
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (e : Fin b.input.k),
  @Eq.{1} (Fin b.input.n → Real)
    (DecrAlmostLinearSSSP.Decremental.initialGradientThrough b
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val b.input.k e)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    fun v =>
    @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (DecrAlmostLinearSSSP.Decremental.initialGradientThrough b (@Fin.val b.input.k e) v)
        (@ite.{1} Real
          (@Eq.{1} (Fin b.input.n) v
            (@DecrAlmostLinearSSSP.Decremental.Digraph.tail b.input.n b.input.k b.input.graph e))
          (instDecidableEqFin b.input.n v
            (@DecrAlmostLinearSSSP.Decremental.Digraph.tail b.input.n b.input.k b.input.graph e))
          (DecrAlmostLinearSSSP.Decremental.capacity b (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
            (DecrAlmostLinearSSSP.Decremental.initialLabel b)
            (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
      (@ite.{1} Real
        (@Eq.{1} (Fin b.input.n) v (@DecrAlmostLinearSSSP.Decremental.Digraph.head b.input.n b.input.k b.input.graph e))
        (instDecidableEqFin b.input.n v
          (@DecrAlmostLinearSSSP.Decremental.Digraph.head b.input.n b.input.k b.input.graph e))
        (DecrAlmostLinearSSSP.Decremental.capacity b (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
          (DecrAlmostLinearSSSP.Decremental.initialLabel b)
          (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  @Eq.{1} (Fin b.input.n → Real)
    (DecrAlmostLinearSSSP.Decremental.initialGradientThrough b
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b)
          (@DFunLike.coe.{1, 1, 1}
            (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
              (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
            (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
            (@EquivLike.toFunLike.{1, 1, 1}
              (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
              (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
              (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
            (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) e))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    fun v =>
    @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
        (DecrAlmostLinearSSSP.Decremental.initialGradientThrough b
          (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b)
            (@DFunLike.coe.{1, 1, 1}
              (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
              (DecrAlmostLinearSSSP.Decremental.Edge b) (fun x => Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
              (@EquivLike.toFunLike.{1, 1, 1}
                (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                  (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                (DecrAlmostLinearSSSP.Decremental.Edge b) (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                  (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
              (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) e))
          v)
        (@ite.{1} Real (@Eq.{1} (Fin b.input.n) v (DecrAlmostLinearSSSP.Decremental.tail b e))
          (instDecidableEqFin b.input.n v (DecrAlmostLinearSSSP.Decremental.tail b e))
          (DecrAlmostLinearSSSP.Decremental.capacity b (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
            (DecrAlmostLinearSSSP.Decremental.initialLabel b) e)
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
      (@ite.{1} Real (@Eq.{1} (Fin b.input.n) v (DecrAlmostLinearSSSP.Decremental.head b e))
        (instDecidableEqFin b.input.n v (DecrAlmostLinearSSSP.Decremental.head b e))
        (DecrAlmostLinearSSSP.Decremental.capacity b (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
          (DecrAlmostLinearSSSP.Decremental.initialLabel b) e)
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @Eq.{1} (Fin b.input.n → Real)
    (DecrAlmostLinearSSSP.Decremental.initialGradientThrough b (DecrAlmostLinearSSSP.Decremental.logicalCount b))
    (DecrAlmostLinearSSSP.Decremental.gradient b
      (DecrAlmostLinearSSSP.Decremental.capacity b (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
        (DecrAlmostLinearSSSP.Decremental.initialLabel b)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
      DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554))))
              (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                    (@DFunLike.coe.{1, 1, 1}
                      (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                      (DecrAlmostLinearSSSP.Decremental.Edge b)
                      (fun x => Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                      (@EquivLike.toFunLike.{1, 1, 1}
                        (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                          (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                        (DecrAlmostLinearSSSP.Decremental.Edge b)
                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                        (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                          (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                      (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)))) →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
                  (@Fin.val b.input.n
                    (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)) →
                (∀ (u : Fin b.input.n),
                    @Eq.{1} Nat (s.natMem (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B u))
                      (DecrAlmostLinearSSSP.Decremental.indegree b u)) →
                  @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image b.input.n
                      (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
                      (DecrAlmostLinearSSSP.Decremental.initialGradientThrough b
                        (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                          (@DFunLike.coe.{1, 1, 1}
                            (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                              (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                            (DecrAlmostLinearSSSP.Decremental.Edge b)
                            (fun x => Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                            (@EquivLike.toFunLike.{1, 1, 1}
                              (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                              (DecrAlmostLinearSSSP.Decremental.Edge b)
                              (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                              (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                            (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                            (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v))))
                      s →
                    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))))
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                        ∃ cost t,
                          And
                            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                              DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.nonsourceCode s cost t)
                            (And
                              (@LE.le.{0} Nat instLENat cost
                                (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))))
                              (And
                                (DecrAlmostLinearSSSP.Decremental.CoreRecord.Initialized b B
                                  (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)
                                  t)
                                (And
                                  (∀ (u : Fin b.input.n),
                                    @Eq.{1} Nat
                                      (t.natMem (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B u))
                                      (DecrAlmostLinearSSSP.Decremental.indegree b u))
                                  (And
                                    (@DecrAlmostLinearSSSP.Decremental.CoreGradient.Image b.input.n
                                      (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
                                      (DecrAlmostLinearSSSP.Decremental.initialGradientThrough b
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                            (@DFunLike.coe.{1, 1, 1}
                                              (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                              (DecrAlmostLinearSSSP.Decremental.Edge b)
                                              (fun x => Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                              (@EquivLike.toFunLike.{1, 1, 1}
                                                (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                  (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                  (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                              (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                                              (@Sum.inr.{0, 0} (Fin b.input.k)
                                                (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                      t)
                                    (And
                                      (@Eq.{1} Nat
                                        (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Fin.val (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                              (@DFunLike.coe.{1, 1, 1}
                                                (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                  (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                (fun x => Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                (@EquivLike.toFunLike.{1, 1, 1}
                                                  (Equiv.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                    (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                  (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                  (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                  (@Equiv.instEquivLike.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                    (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                                (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                                                (@Sum.inr.{0, 0} (Fin b.input.k)
                                                  (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                      (And
                                        (@Eq.{1} Nat
                                          (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@Fin.val b.input.n
                                              (@Subtype.val.{1} (Fin b.input.n)
                                                (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                        (And
                                          (@Eq.{1} ENNReal
                                            (DecrAlmostLinearSSSP.Decremental.stored t.machine
                                              (@Fin.val b.input.n
                                                (@Subtype.val.{1} (Fin b.input.n)
                                                  (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)))
                                            (DecrAlmostLinearSSSP.Decremental.readout b
                                              (DecrAlmostLinearSSSP.Decremental.initialLabel b
                                                (@Subtype.val.{1} (Fin b.input.n)
                                                  (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))))
                                          (And
                                            (@LE.le.{0} Nat instLENat
                                              (t.natMem
                                                (@Fin.val b.input.n
                                                  (@Subtype.val.{1} (Fin b.input.n)
                                                    (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)))
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            (And
                                              (@Eq.{1} Nat
                                                  (t.natMem
                                                    (@Fin.val b.input.n
                                                      (@Subtype.val.{1} (Fin b.input.n)
                                                        (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)))
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                                                @LE.le.{0} Real Real.instLE
                                                  (@OfNat.ofNat.{0} Real (nat_lit 0)
                                                    (@Zero.toOfNat0.{0} Real Real.instZero))
                                                  (t.realMem
                                                    (@Fin.val b.input.n
                                                      (@Subtype.val.{1} (Fin b.input.n)
                                                        (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))))
                                              (DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnEdgeFrame b B v s
                                                t)))))))))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (upto : Nat) (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InitialPublic b upto s →
    @Eq.{1} Nat upto (@Fin.val b.input.n b.input.source) →
      @Eq.{1} (Nat → Nat) t.natMem s.natMem →
        @Eq.{1} (Nat → Real) t.realMem s.realMem →
          DecrAlmostLinearSSSP.Decremental.InitialPublic b
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            t) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B upto : Nat) (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.InitialPublic b upto s →
      @Eq.{1} Nat
          (@Fin.val b.input.n (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))
          upto →
        DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnEdgeFrame b B v s t →
          @Eq.{1} ENNReal
              (DecrAlmostLinearSSSP.Decremental.stored t.machine
                (@Fin.val b.input.n
                  (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)))
              (DecrAlmostLinearSSSP.Decremental.readout b
                (DecrAlmostLinearSSSP.Decremental.initialLabel b
                  (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))) →
            And
                (@LE.le.{0} Nat instLENat
                  (t.natMem
                    (@Fin.val b.input.n
                      (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (@Eq.{1} Nat
                    (t.natMem
                      (@Fin.val b.input.n
                        (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
                  @LE.le.{0} Real Real.instLE
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    (t.realMem
                      (@Fin.val b.input.n
                        (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)))) →
              DecrAlmostLinearSSSP.Decremental.InitialPublic b
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                t) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @Eq.{1} Nat
    (DecrAlmostLinearSSSP.Decremental.returnsBefore b (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (upto : Nat),
  @Eq.{1} Nat
    (DecrAlmostLinearSSSP.Decremental.returnsBefore b
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (DecrAlmostLinearSSSP.Decremental.returnsBefore b upto)
      (@ite.{1} Nat (@Eq.{1} Nat upto (@Fin.val b.input.n b.input.source))
        (instDecidableEqNat upto (@Fin.val b.input.n b.input.source))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @Eq.{1} Nat (DecrAlmostLinearSSSP.Decremental.returnsBefore b b.input.n)
    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) b.input.n
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b),
  @Eq.{1} Nat
    (@Fin.val
      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) b.input.n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      (DecrAlmostLinearSSSP.Decremental.returnIndex b v))
    (DecrAlmostLinearSSSP.Decremental.returnsBefore b
      (@Fin.val b.input.n (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b),
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
      (DecrAlmostLinearSSSP.Decremental.returnsBefore b
        (@Fin.val b.input.n (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (upto : Nat),
  @LE.le.{0} Nat instLENat upto b.input.n →
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.k
        (DecrAlmostLinearSSSP.Decremental.returnsBefore b upto))
      (DecrAlmostLinearSSSP.Decremental.logicalCount b)))))))) ∧ ((((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.body s cost
        t →
      DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input t) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.body s cost
        t →
      DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K t)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.body s cost
        t →
      DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B t) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K upto s →
    @LT.lt.{0} Nat instLTNat upto b.input.n →
      @Eq.{1} Nat upto (@Fin.val b.input.n b.input.source) →
        ∃ t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.body
              s (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) t)
            (And
              (DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                t)
              (DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B s t))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K upto s →
      @LT.lt.{0} Nat instLTNat upto b.input.n →
        @Ne.{1} Nat upto (@Fin.val b.input.n b.input.source) →
          ∃ cost t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.body s cost t)
              (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 87) (instOfNatNat (nat_lit 87))))
                (And
                  (DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                    t)
                  (DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B s t)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K upto s →
      @LT.lt.{0} Nat instLTNat upto b.input.n →
        ∃ cost t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.body
              s cost t)
            (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 87) (instOfNatNat (nat_lit 87))))
              (And
                (DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  t)
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B s t))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LE.le.{0} Nat instLENat b.input.n B →
    DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K upto s →
      ∃ cost t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.loop s
            cost t)
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 89) (instOfNatNat (nat_lit 89)))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) b.input.n upto))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (And (DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K b.input.n t)
              (DecrAlmostLinearSSSP.Decremental.CoreMemory.ReturnFrame b B s t)))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K b.input.n s →
    DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B (DecrAlmostLinearSSSP.Decremental.initializeState b) s) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K b.input.n s →
    @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image b.input.n
      (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
      (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b (DecrAlmostLinearSSSP.Decremental.initializeState b)) s))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K b.input.n s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (DecrAlmostLinearSSSP.Decremental.logicalCount b))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K b.input.n s →
    And
      (∀ (u : Fin b.input.n),
        @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val b.input.n u))
          (@DecrAlmostLinearSSSP.Decremental.State.output b (DecrAlmostLinearSSSP.Decremental.initializeState b) u))
      (∀ (u : Fin b.input.n),
        And
          (@LE.le.{0} Nat instLENat (s.natMem (@Fin.val b.input.n u))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq.{1} Nat (s.natMem (@Fin.val b.input.n u)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (s.realMem (@Fin.val b.input.n u)))))) ∧ ((∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552))))
        (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 662) (instOfNatNat (nat_lit 662))) k))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code k) ∧ ((∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 602) (instOfNatNat (nat_lit 602))))
      (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))))
        (Or (@Eq.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))
          (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) k))) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code k) ∧ (@Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code)
  Bool.true)))) ∧ (((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code
    (DecrAlmostLinearSSSP.Decremental.shadowReg j)) ∧ (∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code
    (DecrAlmostLinearSSSP.Decremental.shadowReg j))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code s cost t →
      DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input t) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (K : Real) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code s cost t →
      DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K t) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code s cost t →
      DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B t)))))) ∧ (((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (e : Fin b.input.k)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.Loaded b B e s →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
      DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.Loaded b B e
        (DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (e : Fin b.input.k)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.Loaded b B e s →
    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 506) (instOfNatNat (nat_lit 506))))
        (DecrAlmostLinearSSSP.Decremental.kappa b) →
      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
          @Eq.{1} Real
            ((DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s).realReg
              (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))))
            (DecrAlmostLinearSSSP.Decremental.capacity b (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
              (DecrAlmostLinearSSSP.Decremental.initialLabel b)
              (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)))) ∧ ((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.code k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 618) (instOfNatNat (nat_lit 618))) →
          DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
            DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.code k))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (e : Fin b.input.k)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreInitializeHeader.Loaded b B e s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 506) (instOfNatNat (nat_lit 506))))
            (DecrAlmostLinearSSSP.Decremental.kappa b) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                  DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.code s
                  (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16)))
                  (DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.result s))
                (And
                  (DecrAlmostLinearSSSP.Decremental.CoreRecord.Initialized b B
                    (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)
                    (DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.result s))
                  (And
                    (@Eq.{1} Real
                      ((DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.result s).realReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))))
                      (DecrAlmostLinearSSSP.Decremental.capacity b
                        (@Finset.univ.{0} (Fin b.input.k) (Fin.fintype b.input.k))
                        (DecrAlmostLinearSSSP.Decremental.initialLabel b)
                        (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)))
                    (∀ (j : Nat),
                      (∀ (offset : Nat),
                          @LT.lt.{0} Nat instLTNat offset
                              (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                            @Ne.{1} Nat j
                              (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B
                                (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)
                                offset)) →
                        And
                          (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.result s).natMem j)
                            (s.natMem j))
                          (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.CoreInitializeStore.result s).realMem j)
                            (s.realMem j)))))) ∧ (∀ {n : Nat} (base counter : Nat) (heads : List.{0} (Fin n)) (g : Fin n → Real) (a z : Fin n) (f : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.CoreDegree.Image n base heads s →
    @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image n base g s →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554)))) base →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) (@Fin.val n a) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628)))) (@Fin.val n z) →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612)))) f →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) counter) →
                      ∃ cost t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            DecrAlmostLinearSSSP.Decremental.CoreInitializeContributions.code s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@OfNat.ofNat.{0} Nat (nat_lit 42) (instOfNatNat (nat_lit 42))))
                            (And
                              (@DecrAlmostLinearSSSP.Decremental.CoreDegree.Image n base
                                (@List.cons.{0} (Fin n) z heads) t)
                              (And
                                (@DecrAlmostLinearSSSP.Decremental.CoreGradient.Image n base
                                  (fun v =>
                                    @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (g v)
                                        (@ite.{1} Real (@Eq.{1} (Fin n) v a) (instDecidableEqFin n v a) f
                                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                                      (@ite.{1} Real (@Eq.{1} (Fin n) v z) (instDecidableEqFin n v z) f
                                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                                  t)
                                (And
                                  (@Eq.{1} Nat
                                    (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) counter
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                  (And
                                    (∀ (j : Nat),
                                      @Ne.{1} Nat j
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              (@Fin.val n z))) →
                                        @Eq.{1} Nat (t.natMem j) (s.natMem j))
                                    (∀ (j : Nat),
                                      @Ne.{1} Nat j
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              (@Fin.val n a))) →
                                        @Ne.{1} Nat j
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                (@Fin.val n z))) →
                                          @Eq.{1} Real (t.realMem j) (s.realMem j))))))))) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 634) (instOfNatNat (nat_lit 634))) →
            @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 662) (instOfNatNat (nat_lit 662))) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
                DecrAlmostLinearSSSP.Decremental.CoreInitializeContributions.code k) ∧ ((∀ {a b c : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval ((a.seq b).seq c) s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval (a.seq (b.seq c)) s cost t) ∧ (∀ {a b c : DecrAlmostLinearSSSP.Decremental.Structured.Cmd} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (a.seq (b.seq c)) s cost t →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval ((a.seq b).seq c) s cost t))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (e : Fin b.input.k)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
      DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B s →
        DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape b.input s →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val b.input.k e)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 652) (instOfNatNat (nat_lit 652))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Fin.val b.input.k e))) →
              @DecrAlmostLinearSSSP.Decremental.CoreDegree.Image b.input.n
                  (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
                  (DecrAlmostLinearSSSP.Decremental.CoreDegree.heads b (@Fin.val b.input.k e)) s →
                @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image b.input.n
                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
                    (DecrAlmostLinearSSSP.Decremental.initialGradientThrough b (@Fin.val b.input.k e)) s →
                  @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))))
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                      ∃ cost t,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@OfNat.ofNat.{0} Nat (nat_lit 83) (instOfNatNat (nat_lit 83))))
                            (And
                              (DecrAlmostLinearSSSP.Decremental.CoreRecord.Initialized b B
                                (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e) t)
                              (And
                                (@DecrAlmostLinearSSSP.Decremental.CoreDegree.Image b.input.n
                                  (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
                                  (DecrAlmostLinearSSSP.Decremental.CoreDegree.heads b
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@Fin.val b.input.k e)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                  t)
                                (And
                                  (@DecrAlmostLinearSSSP.Decremental.CoreGradient.Image b.input.n
                                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
                                    (DecrAlmostLinearSSSP.Decremental.initialGradientThrough b
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@Fin.val b.input.k e)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                    t)
                                  (And
                                    (@Eq.{1} Nat
                                      (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@Fin.val b.input.k e)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                                    (And
                                      (@Eq.{1} Nat
                                        (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 652) (instOfNatNat (nat_lit 652))))
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@Fin.val b.input.k e)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                                      (∀ (j : Nat),
                                        (∀ (offset : Nat),
                                            @LT.lt.{0} Nat instLTNat offset
                                                (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
                                              @Ne.{1} Nat j
                                                (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B
                                                  (@Sum.inl.{0, 0} (Fin b.input.k)
                                                    (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)
                                                  offset)) →
                                          @Ne.{1} Nat j
                                              (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B
                                                (@DecrAlmostLinearSSSP.Decremental.Digraph.tail b.input.n b.input.k
                                                  b.input.graph e)) →
                                            @Ne.{1} Nat j
                                                (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B
                                                  (@DecrAlmostLinearSSSP.Decremental.Digraph.head b.input.n b.input.k
                                                    b.input.graph e)) →
                                              And (@Eq.{1} Nat (t.natMem j) (s.natMem j))
                                                (@Eq.{1} Real (t.realMem j) (s.realMem j)))))))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
      B →
    DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant b B K upto s →
      @LT.lt.{0} Nat instLTNat upto b.input.k →
        ∃ cost t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.code s
              cost t)
            (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 83) (instOfNatNat (nat_lit 83))))
              (And
                (DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant b B K
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  t)
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B s t))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (upto : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
      B →
    DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant b B K upto s →
      ∃ cost t,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.loop s
            cost t)
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 85) (instOfNatNat (nat_lit 85)))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) b.input.k upto))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (And (DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant b B K b.input.k t)
              (DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B s t)))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.startCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.started s)) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 652) (instOfNatNat (nat_lit 652))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.startCode
        k)))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))) →
      DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
        DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.startCode k) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.startCode)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
    DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
      DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B s →
        DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape b.input s →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
            (∀ (v : Fin b.input.n),
                And
                  (@Eq.{1} Nat (s.natMem (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B v))
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@Eq.{1} Real (s.realMem (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B v))
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
              DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant b B K
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.started s)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b.input.n
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) b.input.k))
      B →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured b.input s →
      DecrAlmostLinearSSSP.Decremental.CoreParameters.Values b K s →
        DecrAlmostLinearSSSP.Decremental.CoreControl.Layout b B s →
          DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape b.input s →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
              (∀ (v : Fin b.input.n),
                  And
                    (@Eq.{1} Nat (s.natMem (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B v))
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                    (@Eq.{1} Real (s.realMem (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B v))
                      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) →
                ∃ cost t,
                  And
                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                      DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.corePassCode s cost t)
                    (And
                      (@LE.le.{0} Nat instLENat cost
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 85) (instOfNatNat (nat_lit 85))) b.input.k)
                          (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
                      (And (DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant b B K b.input.k t)
                        (DecrAlmostLinearSSSP.Decremental.CoreMemory.Frame b B s t)))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreInitializeEdge.Invariant b B K b.input.k s →
    @Eq.{1} Nat (s.natMem (@Fin.val b.input.n b.input.source))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
      @Eq.{1} Real (s.realMem (@Fin.val b.input.n b.input.source))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        DecrAlmostLinearSSSP.Decremental.CoreInitializeReturn.Invariant b B K
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
          { realReg := s.realReg,
            natReg :=
              @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))),
            realMem := s.realMem, natMem := s.natMem })))))))) := by sorry
