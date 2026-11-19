-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_2
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T17:33:20.577526+00:00
-- url     : https://prove2.me/theorems/e2cde11e-6f8a-46be-a800-25b1b0e96de9
-- title:
--   Full normalization adapter and core parameter bounds
-- statement:
--   Let the graph, labels, caches, cut states and scalar RAM machines be the objects of the normalized decremental SSSP implementation interface. Each component below is universally quantified over its own parameters and representation hypotheses.
--
--   The native normalization program constructs the augmented input tape, forwards original deletion identifiers, and maintains a public array by instrumenting actual source stores. Coupled online executions preserve every completed prefix and charge initialization, dispatch, callbacks and external requests. The resulting adapter transfers a normalized-core maintenance guarantee to the original polynomial-weight input. The remaining contracts establish the core parameter and initial-label inequalities needed by the internal algorithm.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_2 : (((((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (B : Nat),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88))))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
      @LE.le.{0} Nat instLENat B (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82)))) →
        ∀ (a : Nat),
          @LT.lt.{0} Nat instLTNat a B →
            And (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s).natMem a) (s.natMem a))
              (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s).realMem a) (s.realMem a))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i
      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.fieldData s))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i
      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headData s)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B logical a0 a1 a2 : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (natural : Nat → Nat) (real : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) s
      natural real →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
          (DecrAlmostLinearSSSP.Decremental.bankAddress B (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
            logical) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88))))
            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
          @LE.le.{0} Nat instLENat
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              B →
            @Eq.{1} Nat (s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))) a0 →
              @Eq.{1} Nat
                  (s.natMem
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                  a1 →
                @Eq.{1} Nat
                    (s.natMem
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    a2 →
                  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B
                    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s)
                    (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                      (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat natural logical a0)
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@ite.{1} Nat (@Eq.{1} Nat a1 (@Fin.val i.n i.source))
                          (instDecidableEqNat a1 (@Fin.val i.n i.source)) i.n a1))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      a2)
                    real))) ∧ (((∀ (f : Nat → Nat) (bound : Nat),
  @Eq.{1} (Nat → Nat)
    (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
      (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (DecrAlmostLinearSSSP.Decremental.Normalize.natPrefix f bound) bound (f bound))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bound
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (f
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bound
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bound
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (f
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bound
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
    (DecrAlmostLinearSSSP.Decremental.Normalize.natPrefix f
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) bound
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (e : Fin i.k),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).natMem
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Fin.val i.k e))))
    (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.tail i.n i.k i.graph e)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (e : Fin i.k),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).natMem
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Fin.val i.k e)))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@ite.{1} Nat
      (@Eq.{1} Nat (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e))
        (@Fin.val i.n i.source))
      (instDecidableEqNat (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e))
        (@Fin.val i.n i.source))
      i.n (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (e : Fin i.k),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).natMem
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Fin.val i.k e)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (i.weight e)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (v : Fin i.n),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).natMem
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k (@Fin.val i.n v)))))
    (@Fin.val i.n i.source)))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (v : Fin i.n),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).natMem
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k (@Fin.val i.n v))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    (@ite.{1} Nat (@LT.lt.{0} Nat instLTNat (@Fin.val i.n v) (@Fin.val i.n i.source))
      ((@Fin.val i.n v).decLt (@Fin.val i.n i.source)) (@Fin.val i.n v)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@Fin.val i.n v)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program) (v : Fin i.n),
  @Eq.{1} Nat
    ((DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).natMem
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k (@Fin.val i.n v))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (DecrAlmostLinearSSSP.Decremental.Normalize.sentinel i))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program),
  @Eq.{1} (Nat → Nat)
    (DecrAlmostLinearSSSP.Decremental.Normalize.natPrefix
      (DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).natMem
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
    fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program),
  @Eq.{1} (Nat → Nat)
    (DecrAlmostLinearSSSP.Decremental.Normalize.natPrefix
      (DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).natMem
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))))
    (DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).natMem))) ∧ (((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B : Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.CopyInvariant i p B s →
    @LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90)))) i.k →
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.CopyInvariant i p B
        (DecrAlmostLinearSSSP.Decremental.Normalize.Native.recordData s)) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B : Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.CopyInvariant i p B s →
    ∃ cost t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyLoop s
          cost t)
        (And
          (@LE.le.{0} Nat instLENat cost
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23)))
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) i.k
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (And (DecrAlmostLinearSSSP.Decremental.Normalize.Native.CopyInvariant i p B t)
            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90)))) i.k))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 76) (instOfNatNat (nat_lit 76))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))
          (DecrAlmostLinearSSSP.Decremental.Normalize.sentinel i) →
        (∀ (j : Nat),
            @Eq.{1} Nat (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
          (∀ (j : Nat),
              @Eq.{1} Real (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) →
            DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p
              (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerData p.initPC s)) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStart s
    (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStarted s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStarted s).natMem s.natMem)
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStarted s).realMem s.realMem))))))) ∧ (((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStart k) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStart k)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 76) (instOfNatNat (nat_lit 76))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      (DecrAlmostLinearSSSP.Decremental.SourceMemory.Image
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) s
          (fun x => @OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) fun x =>
          @OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        (∀ (a : Nat),
            @LT.lt.{0} Nat instLTNat a
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
              @Eq.{1} Nat (s.natMem a) ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem a)) →
          DecrAlmostLinearSSSP.Decremental.Normalize.Native.CopyInvariant i p
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStarted s)) ∧ (DecrAlmostLinearSSSP.Decremental.Structured.NoRealMemory DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyLoop))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  ∃ cost,
    And
      (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelBody s
        cost (DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelData s))
      (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))))) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88))))
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        And
          (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelData s).natMem
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                  (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72))))))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@ite.{1} Nat
                      (@LT.lt.{0} Nat instLTNat
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))))
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
                      ((s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90)))).decLt
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))))
                      (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92))))
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))))))
          (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelData s).realMem s.realMem))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 88) (instOfNatNat (nat_lit 88))))
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
      And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelData s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))))
            (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92))))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelData s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))))
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p s →
    (∀ (k : Nat),
        @LE.le.{0} Nat instLENat k (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17))) →
          @Eq.{1} Nat (t.natReg k) (s.natReg k)) →
      (∀ (j : Nat),
          @Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
            (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))) →
        @Eq.{1} (Nat → Real) t.realReg s.realReg → DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p t) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p s →
    DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p
      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyStarted s)))))) ∧ ((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.copyLoop s cost
        t →
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p t) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 82) (instOfNatNat (nat_lit 82))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 84) (instOfNatNat (nat_lit 84))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
            DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelBody k)) ∧ ((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelBody k) ∧ ((DecrAlmostLinearSSSP.Decremental.Structured.NoRealMemory DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelBody) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i
      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelData s))))) ∧ (((∀ {B logical a0 a1 a2 j : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {natural : Nat → Nat}
  {real : Nat → Real},
  DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) s
      natural real →
    @Eq.{1} (Nat → Nat) t.natMem
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem
                (DecrAlmostLinearSSSP.Decremental.bankAddress B
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) logical)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a0))
              (DecrAlmostLinearSSSP.Decremental.bankAddress B
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a1))
            (DecrAlmostLinearSSSP.Decremental.bankAddress B
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a2))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          j) →
      @Eq.{1} (Nat → Real) t.realMem s.realMem →
        DecrAlmostLinearSSSP.Decremental.SourceMemory.Image B
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) t
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat natural logical a0)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              a1)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) logical
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            a2)
          real) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B : Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant i p B s →
    @LT.lt.{0} Nat instLTNat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90)))) i.n →
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant i p B
        (DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelData s))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program} {B : Nat}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant i p B s →
    ∃ cost t,
      And
        (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelLoop
          s cost t)
        (And
          (@LE.le.{0} Nat instLENat cost
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) i.n
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))))))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (And (DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant i p B t)
            (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90)))) i.n)))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {cost : Nat},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelLoop s
        cost t →
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p t) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelStart s
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelStarted s)))))))) ∧ ((((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 92) (instOfNatNat (nat_lit 92))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame
        DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelStart k) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelStart
    k)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.CopyInvariant i p
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90)))) i.k →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 78) (instOfNatNat (nat_lit 78))))
          (DecrAlmostLinearSSSP.Decremental.Normalize.sentinel i) →
        DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant i p
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelStarted s)) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p s →
    DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p
      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.sentinelStarted s)))) ∧ (((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} (entry : Nat) {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i s →
    DecrAlmostLinearSSSP.Decremental.InputCapture.Captured i
      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.headerData entry s)) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B a : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.some.{0} Nat a) s g →
    @LT.lt.{0} Nat instLTNat a i.n →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
          DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              s g →
            DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat)
              (DecrAlmostLinearSSSP.Decremental.Normalize.Native.committed s) g)) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B a : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.some.{0} Nat a) s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) a))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) s
            g →
          ∃ cost t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                DecrAlmostLinearSSSP.Decremental.Normalize.Native.callback s cost t)
              (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
                (And
                  (DecrAlmostLinearSSSP.Decremental.ShadowDataRep B
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) t g)
                  (DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat) t g)))) ∧ ((∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (g : DecrAlmostLinearSSSP.Decremental.Machine) (v : Nat),
  @Ne.{1} (Option.{0} Nat) (DecrAlmostLinearSSSP.Decremental.Normalize.Native.writtenAddress ins g)
      (@Option.some.{0} Nat v) →
    And (@Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.instructionEffect ins g).natMem v) (g.natMem v))
      (@Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.instructionEffect ins g).realMem v) (g.realMem v))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat) s g →
    DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) s g →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
          ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (cost : Nat),
            DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.shadowAction ins) s cost
                t →
              DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B
                (DecrAlmostLinearSSSP.Decremental.Normalize.Native.writtenAddress ins g) t
                (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g)))))) ∧ ((((∀ {B F : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
        ∀ (a d cost : Nat),
          DecrAlmostLinearSSSP.Decremental.Structured.Eval
              (DecrAlmostLinearSSSP.Decremental.shadowAction (DecrAlmostLinearSSSP.Decremental.Instruction.store a d)) s
              cost t →
            @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))) ∧ (∀ {B F : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F s g →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) F →
        ∀ (a d cost : Nat),
          DecrAlmostLinearSSSP.Decremental.Structured.Eval
              (DecrAlmostLinearSSSP.Decremental.shadowAction (DecrAlmostLinearSSSP.Decremental.Instruction.storeN a d))
              s cost t →
            @Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (g.natReg a))
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) ∧ ((∀ {B F : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F s g →
    ∀ (ins : DecrAlmostLinearSSSP.Decremental.Instruction) (cost : Nat),
      DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.shadowAction ins) s cost t →
        DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F t
            (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g) →
          DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F t
            (DecrAlmostLinearSSSP.Decremental.instructionEffect ins g)) ∧ ((∀ {B F : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F s g →
    ∀ (cost : Nat),
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Normalize.Native.callback s cost
          t →
        DecrAlmostLinearSSSP.Decremental.ShadowDataRep B F t g →
          DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B F t g) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (B : Nat),
  DecrAlmostLinearSSSP.Decremental.Instrumented.ActionSpec DecrAlmostLinearSSSP.Decremental.Normalize.Native.action
    DecrAlmostLinearSSSP.Decremental.Normalize.Native.bound
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat)) B
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) ∧ (((∀ (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Structured.NoRealMemory
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.bootCode p)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (host p : DecrAlmostLinearSSSP.Decremental.Program),
      ∃ cost s,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
            (DecrAlmostLinearSSSP.Decremental.Normalize.Native.bootCode p)
            (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine host i))
            cost s)
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))) i.size)
                (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))))
            (And (DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p s)
              (And
                (DecrAlmostLinearSSSP.Decremental.Normalize.Native.SentinelInvariant i p
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  s)
                (@Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 90) (instOfNatNat (nat_lit 90)))) i.n)))))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Nat),
  @LT.lt.{0} Nat instLTNat a i.n →
    @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem a)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {p : DecrAlmostLinearSSSP.Decremental.Program}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Registers i p s →
    DecrAlmostLinearSSSP.Decremental.SourceMemory.Image
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) s
        (DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).natMem
        (DecrAlmostLinearSSSP.Decremental.initialMachine p
            (DecrAlmostLinearSSSP.Decremental.Normalize.input i)).realMem →
      DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) s
        (DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (host p : DecrAlmostLinearSSSP.Decremental.Program),
      ∃ cost s,
        And
          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
            (DecrAlmostLinearSSSP.Decremental.Normalize.Native.bootCode p)
            (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine host i))
            cost s)
          (And
            (@LE.le.{0} Nat instLENat cost
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50))) i.size)
                (@OfNat.ofNat.{0} Nat (nat_lit 100) (instOfNatNat (nat_lit 100)))))
            (And
              (DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) s
                (DecrAlmostLinearSSSP.Decremental.initialMachine p
                  (DecrAlmostLinearSSSP.Decremental.Normalize.input i)))
              (DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Option.none.{0} Nat) s
                (DecrAlmostLinearSSSP.Decremental.initialMachine p
                  (DecrAlmostLinearSSSP.Decremental.Normalize.input i))))))))))) ∧ (((((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (e : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval (DecrAlmostLinearSSSP.Decremental.Normalize.Native.updateHeader p)
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.externallySupplied s e)
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.updateStarted p s e)) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (B : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (e : Nat),
  DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) s g →
    DecrAlmostLinearSSSP.Decremental.Instrumented.MachineRep B
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.updateStarted p s e)
      (DecrAlmostLinearSSSP.Decremental.deletionMachine p g e))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {B : Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  {g : DecrAlmostLinearSSSP.Decremental.Machine},
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat) s g →
    ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (e : Nat),
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.Image i B (@Option.none.{0} Nat)
        (DecrAlmostLinearSSSP.Decremental.Normalize.Native.updateStarted p s e)
        (DecrAlmostLinearSSSP.Decremental.deletionMachine p g e)) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (c : DecrAlmostLinearSSSP.Decremental.Machine) (v : Nat),
  ∃ d,
    And
      (DecrAlmostLinearSSSP.Decremental.Ends (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p)
        (have __src :=
          DecrAlmostLinearSSSP.Decremental.resume c (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p).query;
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
            (And (@Eq.{1} (Nat → Real) d.realMem c.realMem) (@Eq.{1} (Nat → Nat) d.natMem c.natMem)))))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
      ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (g : DecrAlmostLinearSSSP.Decremental.Machine),
        DecrAlmostLinearSSSP.Decremental.Ends p
            (DecrAlmostLinearSSSP.Decremental.initialMachine p (DecrAlmostLinearSSSP.Decremental.Normalize.input i)) g →
          ∃ c,
            And
              (DecrAlmostLinearSSSP.Decremental.Ends (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p)
                (DecrAlmostLinearSSSP.Decremental.initialMachine
                  (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p) i)
                c)
              (And (DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i c g)
                (@LE.le.{0} Nat instLENat c.work
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (DecrAlmostLinearSSSP.Decremental.Normalize.Native.dispatchCost p) g.work)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) i.size))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (p : DecrAlmostLinearSSSP.Decremental.Program)
  (c g g' : DecrAlmostLinearSSSP.Decremental.Machine) (e : Nat),
  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i c g →
    DecrAlmostLinearSSSP.Decremental.Ends p (DecrAlmostLinearSSSP.Decremental.deletionMachine p g e) g' →
      ∃ d,
        And
          (DecrAlmostLinearSSSP.Decremental.Ends (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p)
            (DecrAlmostLinearSSSP.Decremental.deletionMachine
              (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p) c e)
            d)
          (And (DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i d g')
            (@LE.le.{0} Nat instLENat d.work
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.dispatchCost p)
                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) g'.work g.work)))
                (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
      ∀ (p : DecrAlmostLinearSSSP.Decremental.Program)
        {sourceDs : List.{0} (Fin (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k)}
        {sourceCs : List.{0} DecrAlmostLinearSSSP.Decremental.Machine},
        DecrAlmostLinearSSSP.Decremental.OnlineRun p (DecrAlmostLinearSSSP.Decremental.Normalize.input i) sourceDs
            sourceCs →
          ∀ (ds : List.{0} (Fin i.k)),
            @Eq.{1} (List.{0} (Fin (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k)) sourceDs
                (@List.map.{0, 0} (Fin i.k)
                  (Fin (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.k i.n))
                  (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i) ds) →
              ∃ cs c g,
                And
                  (DecrAlmostLinearSSSP.Decremental.OnlineRun
                    (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p) i ds cs)
                  (And
                    (@Eq.{1} Nat (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
                      (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine sourceCs))
                    (And
                      (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                        (@List.getLast?.{0} DecrAlmostLinearSSSP.Decremental.Machine cs)
                        (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine c))
                      (And
                        (@Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                          (@List.getLast?.{0} DecrAlmostLinearSSSP.Decremental.Machine sourceCs)
                          (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine g))
                        (And (DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i c g)
                          (And
                            (@LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c.work
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                                  (@List.length.{0} (Fin i.k) ds)))
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (DecrAlmostLinearSSSP.Decremental.Normalize.Native.dispatchCost p)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) g.work
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
                                      (@List.length.{0} (Fin i.k) ds))))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200))) i.size)))
                            (∀ (j : Nat) (c' g' : DecrAlmostLinearSSSP.Decremental.Machine),
                              @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                  (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine) Nat
                                    DecrAlmostLinearSSSP.Decremental.Machine
                                    (fun as i =>
                                      @LT.lt.{0} Nat instLTNat i
                                        (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine as))
                                    (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Machine) cs j)
                                  (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine c') →
                                @Eq.{1} (Option.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                    (@GetElem?.getElem?.{0, 0, 0} (List.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                      Nat DecrAlmostLinearSSSP.Decremental.Machine
                                      (fun as i =>
                                        @LT.lt.{0} Nat instLTNat i
                                          (@List.length.{0} DecrAlmostLinearSSSP.Decremental.Machine as))
                                      (@List.instGetElem?NatLtLength.{0} DecrAlmostLinearSSSP.Decremental.Machine)
                                      sourceCs j)
                                    (@Option.some.{0} DecrAlmostLinearSSSP.Decremental.Machine g') →
                                  DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i c' g'))))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {c g : DecrAlmostLinearSSSP.Decremental.Machine},
  i.Valid →
    ∀ (ds : List.{0} (Fin i.k)),
      DecrAlmostLinearSSSP.Decremental.Normalize.Native.Boundary i c g →
        DecrAlmostLinearSSSP.Decremental.Normalize.Native.Correct (DecrAlmostLinearSSSP.Decremental.Normalize.input i)
            (@List.map.{0, 0} (Fin i.k) (Fin (DecrAlmostLinearSSSP.Decremental.Normalize.input i).k)
              (DecrAlmostLinearSSSP.Decremental.Normalize.oldEdge i) ds)
            g →
          DecrAlmostLinearSSSP.Decremental.Normalize.Native.Correct i ds c) ∧ (∀ (a : Nat → Real),
  DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
    DecrAlmostLinearSSSP.Decremental.Subpolynomial (DecrAlmostLinearSSSP.Decremental.Normalize.Native.overhead a)))))) ∧ ((((∀ (H G M D C A eps : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) M →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) D →
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) A →
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eps →
            @LE.le.{0} Real Real.instLE eps (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
              @LE.le.{0} Real Real.instLE H
                  (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) D G)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 200)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 200) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat
                            (@OfNat.ofNat.{0} Nat (nat_lit 199) (instOfNatNat (nat_lit 199)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 198) (instOfNatNat (nat_lit 198)))))))
                      M)) →
                @LE.le.{0} Real Real.instLE G
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C
                          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                            (@OfNat.ofNat.{0} Real (nat_lit 4)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                            M))
                        A)
                      eps) →
                  @LE.le.{0} Real Real.instLE H
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@OfNat.ofNat.{0} Real (nat_lit 4)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                                D)
                              C)
                            (@OfNat.ofNat.{0} Real (nat_lit 200)
                              (@instOfNatAtLeastTwo.{0} Real (nat_lit 200) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 199) (instOfNatNat (nat_lit 199)))
                                  (@Nat.instNeZeroSucc
                                    (@OfNat.ofNat.{0} Nat (nat_lit 198) (instOfNatNat (nat_lit 198))))))))
                          M)
                        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) A))
                      eps)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) i.n →
      ∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (C : Real) (a : Nat → Real) (queryBound : Nat),
        @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) C →
          DecrAlmostLinearSSSP.Decremental.Subpolynomial a →
            DecrAlmostLinearSSSP.Decremental.Maintains p C a queryBound Bool.false
                (DecrAlmostLinearSSSP.Decremental.Normalize.input i) →
              DecrAlmostLinearSSSP.Decremental.Maintains (DecrAlmostLinearSSSP.Decremental.Normalize.Native.program p)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                      (@OfNat.ofNat.{0} Real (nat_lit 4)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                      (@Nat.cast.{0} Real Real.instNatCast
                        (DecrAlmostLinearSSSP.Decremental.Normalize.Native.dispatchCost p)))
                    C)
                  (@OfNat.ofNat.{0} Real (nat_lit 200)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 200) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 199) (instOfNatNat (nat_lit 199)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 198) (instOfNatNat (nat_lit 198))))))))
                (DecrAlmostLinearSSSP.Decremental.Normalize.Native.overhead a)
                (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) Bool.false i)) ∧ ((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    @Ne.{1} (Fin n) u v → ∃ e, @Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e) v) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (v : Fin b.input.n),
  @Ne.{1} (Fin b.input.n) v b.input.source →
    @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (DecrAlmostLinearSSSP.Decremental.indegree b v)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE
    (@OfNat.ofNat.{0} Real (nat_lit 32)
      (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
    (DecrAlmostLinearSSSP.Decremental.A b))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@OfNat.ofNat.{0} Real (nat_lit 4)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
      (@Nat.cast.{0} Real Real.instNatCast b.input.n))
    (DecrAlmostLinearSSSP.Decremental.Q b)) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (active : Finset.{0} (Fin b.input.k)) (e : Fin b.input.k),
  And
    (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (DecrAlmostLinearSSSP.Decremental.cost b active
        (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e)))
    (@LE.le.{0} Real Real.instLE
      (DecrAlmostLinearSSSP.Decremental.cost b active
        (@Sum.inl.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) e))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 8)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 8) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))))
          (@Nat.cast.{0} Real Real.instNatCast b.input.n)))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  And
    (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (DecrAlmostLinearSSSP.Decremental.coefficient b e))
    (@LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.coefficient b e)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (DecrAlmostLinearSSSP.Decremental.A b)
        (@Nat.cast.{0} Real Real.instNatCast b.input.size)))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  @LE.le.{0} Real Real.instLE (∑ e, DecrAlmostLinearSSSP.Decremental.coefficient b e)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (DecrAlmostLinearSSSP.Decremental.A b))
      (@HPow.hPow.{0, 0, 0} Real Nat Real
        (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
        (@Nat.cast.{0} Real Real.instNatCast b.input.size)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core),
  And
    (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (DecrAlmostLinearSSSP.Decremental.kappa b))
    (And
      (@LE.le.{0} Real Real.instLE (DecrAlmostLinearSSSP.Decremental.kappa b)
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      (@LE.le.{0} Real Real.instLE
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                (@OfNat.ofNat.{0} Real (nat_lit 4)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                (@Nat.cast.{0} Real Real.instNatCast b.input.n))
              (DecrAlmostLinearSSSP.Decremental.A b))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@Nat.cast.{0} Real Real.instNatCast b.input.size)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (DecrAlmostLinearSSSP.Decremental.kappa b))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))))))))))) := by sorry
