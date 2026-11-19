-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_core_laws_10
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T17:33:32.912798+00:00
-- url     : https://prove2.me/theorems/feb2254d-cc83-4cf1-bf82-82056b723fc4
-- title:
--   Charged refresh, gradient updates, reports and toggles
-- statement:
--   Let the graph, labels, caches, cut states and scalar RAM machines be the objects of the normalized decremental SSSP implementation interface. Each component below is universally quantified over its own parameters and representation hypotheses.
--
--   A full refresh computes the new capacity, changes the physical cut instance, updates the cached gradient and commits the historical/public return sample. Actual toggles scan and deduplicate the emitted reports, retaining complete threshold detection. Operation counts, report volumes, source work and native instruction costs are charged by the stated amortized-credit contracts.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.core_laws_10 : (((((((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.code) ∧ (@Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.code)
  Bool.true)) ∧ ((∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.code k) ∧ (∀ (k : Nat),
  Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 600) (instOfNatNat (nat_lit 600))))
      (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 606) (instOfNatNat (nat_lit 606))) k) →
    DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.code k))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
          (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e) →
        And
          (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
            (DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s))
          (And
            (DecrAlmostLinearSSSP.Decremental.CoreGeometry.Loaded b state e
              (DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s))
            (And
              (DecrAlmostLinearSSSP.Decremental.CoreRecord.Addresses
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                (DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s))
              (And
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 636) (instOfNatNat (nat_lit 636))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.tail b e))))
                (@Eq.{1} Nat
                  ((DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s).natReg
                    (@OfNat.ofNat.{0} Nat (nat_lit 638) (instOfNatNat (nat_lit 638))))
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.head b e)))))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
      g (DecrAlmostLinearSSSP.Decremental.CoreRefreshRead.result s))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
        g s →
      @LE.le.{0} Nat instLENat b.input.n B →
        DecrAlmostLinearSSSP.Decremental.CoreGeometry.Loaded b state e s →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 608) (instOfNatNat (nat_lit 608))))
              (@DecrAlmostLinearSSSP.Decremental.State.y b state (DecrAlmostLinearSSSP.Decremental.tail b e)) →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 610) (instOfNatNat (nat_lit 610))))
                (@DecrAlmostLinearSSSP.Decremental.State.y b state (DecrAlmostLinearSSSP.Decremental.head b e)) →
              And
                (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
                  (DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s))
                (And
                  (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
                    (DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s))
                  (And
                    (@Eq.{1} Real
                      ((DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s).realReg
                        (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))))
                      (DecrAlmostLinearSSSP.Decremental.capacity b
                        (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                        (DecrAlmostLinearSSSP.Decremental.labels b state) e))
                    (And
                      (@Eq.{1} Real
                        ((DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s).realReg
                          (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614))))
                        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                          (DecrAlmostLinearSSSP.Decremental.capacity b
                            (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                            (DecrAlmostLinearSSSP.Decremental.labels b state) e)
                          (@DecrAlmostLinearSSSP.Decremental.State.cache b state e)))
                      (∀ (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b),
                        @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Edge b) e
                            (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v) →
                          @Eq.{1} Real
                            ((DecrAlmostLinearSSSP.Decremental.CoreRefresh.result s).realReg
                              (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616))))
                            (DecrAlmostLinearSSSP.Decremental.labels b state
                              (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source)
                                v))))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (f : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state s →
    DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B
      (@DecrAlmostLinearSSSP.Decremental.State.mk b (@DecrAlmostLinearSSSP.Decremental.State.active b state)
        (@DecrAlmostLinearSSSP.Decremental.State.y b state)
        (@Function.update.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (fun a => Real)
          (fun a b_1 =>
            @instDecidableEqSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
              (instDecidableEqFin b.input.k) (DecrAlmostLinearSSSP.Decremental.instDecidableEqReturnVertex b) a b_1)
          (@DecrAlmostLinearSSSP.Decremental.State.cache b state) e f)
        (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
        (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
        (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
        (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
        (@DecrAlmostLinearSSSP.Decremental.State.output b state)
        (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
        (@DecrAlmostLinearSSSP.Decremental.State.stopped b state)
        (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
        (@DecrAlmostLinearSSSP.Decremental.State.history b state))
      { realReg := s.realReg, natReg := s.natReg,
        realMem :=
          @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
            (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
            f,
        natMem := s.natMem }) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (f : Real) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
        (@DecrAlmostLinearSSSP.Decremental.State.mk b (@DecrAlmostLinearSSSP.Decremental.State.active b state)
          (@DecrAlmostLinearSSSP.Decremental.State.y b state)
          (@Function.update.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b) (fun a => Real)
            (fun a b_1 =>
              @instDecidableEqSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                (instDecidableEqFin b.input.k) (DecrAlmostLinearSSSP.Decremental.instDecidableEqReturnVertex b) a b_1)
            (@DecrAlmostLinearSSSP.Decremental.State.cache b state) e f)
          (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
          (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
          (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
          (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
          (@DecrAlmostLinearSSSP.Decremental.State.output b state)
          (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
          (@DecrAlmostLinearSSSP.Decremental.State.stopped b state)
          (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
          (@DecrAlmostLinearSSSP.Decremental.State.history b state))
        { realReg := s.realReg, natReg := s.natReg,
          realMem :=
            @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem
              (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
              f,
          natMem := s.natMem }))))) ∧ ((((@Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.code)
  Bool.true) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 634) (instOfNatNat (nat_lit 634))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.code k)) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 698) (instOfNatNat (nat_lit 698))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
            DecrAlmostLinearSSSP.Decremental.Structured.RealFrame
              DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.code k) ∧ (∀ {n : Nat} (base : Nat) (g : Fin n → Real) (a z : Fin n) (delta f : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image n base g s →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 554) (instOfNatNat (nat_lit 554)))) base →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626)))) (@Fin.val n a) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628)))) (@Fin.val n z) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614)))) delta →
            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612)))) f →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
                ∃ cost t,
                  And
                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                      DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.code s cost t)
                    (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 39) (instOfNatNat (nat_lit 39))))
                      (And
                        (@DecrAlmostLinearSSSP.Decremental.CoreGradient.Image n base
                          (fun v =>
                            @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (g v)
                                (@ite.{1} Real (@Eq.{1} (Fin n) v a) (instDecidableEqFin n v a) delta
                                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                              (@ite.{1} Real (@Eq.{1} (Fin n) v z) (instDecidableEqFin n v z) delta
                                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                          t)
                        (And
                          (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612)))) f)
                          (And (@Eq.{1} (Nat → Nat) t.natMem s.natMem)
                            (∀ (j : Nat),
                              @Ne.{1} Nat j
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n a))) →
                                @Ne.{1} Nat j
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) base
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (@Fin.val n z))) →
                                  @Eq.{1} Real (t.realMem j) (s.realMem j))))))))) ∧ (((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) {before after : DecrAlmostLinearSSSP.Decremental.State b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B before s →
    @Eq.{1} (Finset.{0} (Fin b.input.k)) (@DecrAlmostLinearSSSP.Decremental.State.active b after)
        (@DecrAlmostLinearSSSP.Decremental.State.active b before) →
      @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Edge b → Real) (@DecrAlmostLinearSSSP.Decremental.State.cache b after)
          (@DecrAlmostLinearSSSP.Decremental.State.cache b before) →
        @Eq.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.sample b after)
            (@DecrAlmostLinearSSSP.Decremental.State.sample b before) →
          DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B after s) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real)
  {before after : DecrAlmostLinearSSSP.Decremental.State b} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K before s →
    @Eq.{1} (Finset.{0} (Fin b.input.k)) (@DecrAlmostLinearSSSP.Decremental.State.active b after)
        (@DecrAlmostLinearSSSP.Decremental.State.active b before) →
      @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Edge b → Real) (@DecrAlmostLinearSSSP.Decremental.State.cache b after)
          (@DecrAlmostLinearSSSP.Decremental.State.cache b before) →
        @Eq.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b after)
            (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b before) →
          @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
              (@DecrAlmostLinearSSSP.Decremental.State.pending b after)
              (@DecrAlmostLinearSSSP.Decremental.State.pending b before) →
            @Eq.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.sample b after)
                (@DecrAlmostLinearSSSP.Decremental.State.sample b before) →
              @Eq.{1} (Fin b.input.n → ENNReal) (@DecrAlmostLinearSSSP.Decremental.State.output b after)
                  (@DecrAlmostLinearSSSP.Decremental.State.output b before) →
                DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K after s)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    (∀ (k : Nat),
        @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
            (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))
              (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 112) (instOfNatNat (nat_lit 112)))
                (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 106) (instOfNatNat (nat_lit 106)))
                  (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))
                    (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56)))
                      (@List.nil.{0} Nat))))))
            k →
          @Eq.{1} Nat (t.natReg k) (s.natReg k)) →
      (∀ (j : Nat),
          @LE.le.{0} Nat instLENat N j →
            And
              (@Eq.{1} Nat (t.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                (s.natReg (DecrAlmostLinearSSSP.Decremental.shadowReg j)))
              (@Eq.{1} Real (t.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j))
                (s.realReg (DecrAlmostLinearSSSP.Decremental.shadowReg j)))) →
        (∀ (address : Nat),
            Not (DecrAlmostLinearSSSP.Decremental.CoreHost.Address b B address) →
              And (@Eq.{1} Nat (t.natMem address) (s.natMem address))
                (@Eq.{1} Real (t.realMem address) (s.realMem address))) →
          DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
            (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g t) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (a z : Fin b.input.n) (delta : Real) (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (cost : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.code s cost
          t →
        @DecrAlmostLinearSSSP.Decremental.CoreGradient.Image b.input.n
            (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientBase b B)
            (fun v =>
              @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                  (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state v)
                  (@ite.{1} Real (@Eq.{1} (Fin b.input.n) v a) (instDecidableEqFin b.input.n v a) delta
                    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                (@ite.{1} Real (@Eq.{1} (Fin b.input.n) v z) (instDecidableEqFin b.input.n v z) delta
                  (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
            t →
          @Eq.{1} (Nat → Nat) t.natMem s.natMem →
            (∀ (j : Nat),
                @Ne.{1} Nat j (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B a) →
                  @Ne.{1} Nat j (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B z) →
                    @Eq.{1} Real (t.realMem j) (s.realMem j)) →
              DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                (@DecrAlmostLinearSSSP.Decremental.State.mk b (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.y b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.cache b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
                  (fun v =>
                    @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                        (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state v)
                        (@ite.{1} Real (@Eq.{1} (Fin b.input.n) v a) (instDecidableEqFin b.input.n v a) delta
                          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                      (@ite.{1} Real (@Eq.{1} (Fin b.input.n) v z) (instDecidableEqFin b.input.n v z) delta
                        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
                  (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.output b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.stopped b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.history b state))
                t) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (a z : Fin b.input.n) (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (cost : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreGradientDelta.code s cost t →
      @Eq.{1} (Nat → Nat) t.natMem s.natMem →
        (∀ (j : Nat),
            @Ne.{1} Nat j (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B a) →
              @Ne.{1} Nat j (DecrAlmostLinearSSSP.Decremental.CoreMemory.gradientCell b B z) →
                @Eq.{1} Real (t.realMem j) (s.realMem j)) →
          DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
            (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g t)))))) ∧ (((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (xs : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
          (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
          (@List.cons.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) e xs) →
        ∃ t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CorePending.popCode s
              (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) t)
            (And
              (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                (@DecrAlmostLinearSSSP.Decremental.State.mk b (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.y b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.cache b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.output b state) xs
                  (@DecrAlmostLinearSSSP.Decremental.State.stopped b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.history b state))
                t)
              (And
                (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                  (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e))
                (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                  (∀ (j : Nat),
                    @Ne.{1} Nat j
                        (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
                          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
                      @Eq.{1} Nat (t.natMem j) (s.natMem j)))))) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    ∀ (address : Nat) (value : Real),
      DecrAlmostLinearSSSP.Decremental.CoreHost.Address b B address →
        DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
          (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
          { realReg := s.realReg, natReg := s.natReg,
            realMem := @Function.update.{1, 1} Nat (fun a => Real) instDecidableEqNat s.realMem address value,
            natMem := s.natMem })) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    ∀ (address value : Nat),
      DecrAlmostLinearSSSP.Decremental.CoreHost.Address b B address →
        DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
          (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
          { realReg := s.realReg, natReg := s.natReg, realMem := s.realMem,
            natMem := @Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem address value }) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (cost : Nat) (e : DecrAlmostLinearSSSP.Decremental.Edge b),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CorePending.popCode s cost t →
      @Eq.{1} (Nat → Real) t.realMem s.realMem →
        (∀ (j : Nat),
            @Ne.{1} Nat j
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
              @Eq.{1} Nat (t.natMem j) (s.natMem j)) →
          DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
            (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g t))) ∧ (((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 550) (instOfNatNat (nat_lit 550))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 620) (instOfNatNat (nat_lit 620))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 632) (instOfNatNat (nat_lit 632))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 634) (instOfNatNat (nat_lit 634))) →
          DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreCommit.prefixCode k) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 698) (instOfNatNat (nat_lit 698))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 630) (instOfNatNat (nat_lit 630))) →
            DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreCommit.prefixCode
              k)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (f delta : Real) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
        g s →
      @LE.le.{0} Nat instLENat b.input.n B →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
            (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
              (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
              (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.tail b e)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))))
                (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.head b e)) →
              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612)))) f →
                @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614)))) delta →
                  ∃ cost t,
                    And
                      (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                        DecrAlmostLinearSSSP.Decremental.CoreCommit.prefixCode s cost t)
                      (And
                        (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))))
                        (And
                          (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                            (DecrAlmostLinearSSSP.Decremental.CoreCommit.cacheGradientState b state e f delta) t)
                          (And
                            (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                              (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g t)
                            (@Eq.{1} Real (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))))
                              f))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b) (r : Real)
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @Eq.{1} Real
          (t.realMem
            (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B
              (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          r →
        (∀ (j : Nat),
            @Ne.{1} Nat j
                (@Fin.val b.input.n
                  (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)) →
              @Eq.{1} Nat (t.natMem j) (s.natMem j)) →
          (∀ (j : Nat),
              @Ne.{1} Nat j
                  (@Fin.val b.input.n
                    (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)) →
                @Ne.{1} Nat j
                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B
                      (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
                  @Eq.{1} Real (t.realMem j) (s.realMem j)) →
            DecrAlmostLinearSSSP.Decremental.CoreGeometry.Image b B
              (@DecrAlmostLinearSSSP.Decremental.State.mk b (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                (@DecrAlmostLinearSSSP.Decremental.State.y b state)
                (@DecrAlmostLinearSSSP.Decremental.State.cache b state)
                (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
                (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
                (@Function.update.{1, 1} (Fin b.input.n) (fun a => Real) (instDecidableEqFin b.input.n)
                  (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
                  (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v) r)
                (@DecrAlmostLinearSSSP.Decremental.State.output b state)
                (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
                (@DecrAlmostLinearSSSP.Decremental.State.stopped b state)
                (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
                (@DecrAlmostLinearSSSP.Decremental.State.history b state))
              t) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b) (r : Real)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
          (@Fin.val b.input.n
            (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 578) (instOfNatNat (nat_lit 578))))
            (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B
              (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
          @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616)))) r →
            ∃ cost t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReturn.code s
                  cost t)
                (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11))))
                  (And
                    (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                      (@DecrAlmostLinearSSSP.Decremental.State.mk b
                        (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.y b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.cache b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
                        (@Function.update.{1, 1} (Fin b.input.n) (fun a => Real) (instDecidableEqFin b.input.n)
                          (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
                          (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v) r)
                        (@Function.update.{1, 1} (Fin b.input.n) (fun a => ENNReal) (instDecidableEqFin b.input.n)
                          (@DecrAlmostLinearSSSP.Decremental.State.output b state)
                          (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)
                          (DecrAlmostLinearSSSP.Decremental.readout b r))
                        (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.stopped b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
                        (@DecrAlmostLinearSSSP.Decremental.State.history b state))
                      t)
                    (And
                      (∀ (j : Nat),
                        @Ne.{1} Nat j
                            (@Fin.val b.input.n
                              (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source)
                                v)) →
                          @Eq.{1} Nat (t.natMem j) (s.natMem j))
                      (∀ (j : Nat),
                        @Ne.{1} Nat j
                            (@Fin.val b.input.n
                              (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source)
                                v)) →
                          @Ne.{1} Nat j
                              (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B
                                (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
                            @Eq.{1} Real (t.realMem j) (s.realMem j)))))))))) ∧ ((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b) (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data)
  (cost : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
      s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReturn.code s cost t →
        (∀ (j : Nat),
            @Ne.{1} Nat j
                (@Fin.val b.input.n
                  (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)) →
              @Eq.{1} Nat (t.natMem j) (s.natMem j)) →
          (∀ (j : Nat),
              @Ne.{1} Nat j
                  (@Fin.val b.input.n
                    (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v)) →
                @Ne.{1} Nat j
                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B
                      (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
                  @Eq.{1} Real (t.realMem j) (s.realMem j)) →
            DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
              (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g t) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
        g s →
      @LE.le.{0} Nat instLENat b.input.n B →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648))))
            (DecrAlmostLinearSSSP.Decremental.CoreGeometry.returnBit b e) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
              (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.tail b e)) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 578) (instOfNatNat (nat_lit 578))))
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
              (∀ (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b),
                  @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Edge b) e
                      (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v) →
                    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616))))
                      (DecrAlmostLinearSSSP.Decremental.labels b state
                        (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source) v))) →
                ∃ cost t,
                  And
                    (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                      DecrAlmostLinearSSSP.Decremental.CoreCommit.returnCode s cost t)
                    (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
                      (And
                        (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                          (DecrAlmostLinearSSSP.Decremental.CoreCommit.returnState b state e) t)
                        (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                          (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g t))))) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (xs : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
        g s →
      @LE.le.{0} Nat instLENat b.input.n B →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
            (@List.cons.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) e xs) →
          @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 568) (instOfNatNat (nat_lit 568))))
              (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
                (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
            @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 626) (instOfNatNat (nat_lit 626))))
                (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.tail b e)) →
              @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 628) (instOfNatNat (nat_lit 628))))
                  (@Fin.val b.input.n (DecrAlmostLinearSSSP.Decremental.head b e)) →
                @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 648) (instOfNatNat (nat_lit 648))))
                    (DecrAlmostLinearSSSP.Decremental.CoreGeometry.returnBit b e) →
                  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 578) (instOfNatNat (nat_lit 578))))
                      (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e
                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
                    @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 612) (instOfNatNat (nat_lit 612))))
                        (DecrAlmostLinearSSSP.Decremental.capacity b
                          (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                          (DecrAlmostLinearSSSP.Decremental.labels b state) e) →
                      @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 614) (instOfNatNat (nat_lit 614))))
                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                            (DecrAlmostLinearSSSP.Decremental.capacity b
                              (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                              (DecrAlmostLinearSSSP.Decremental.labels b state) e)
                            (@DecrAlmostLinearSSSP.Decremental.State.cache b state e)) →
                        (∀ (v : DecrAlmostLinearSSSP.Decremental.ReturnVertex b),
                            @Eq.{1} (DecrAlmostLinearSSSP.Decremental.Edge b) e
                                (@Sum.inr.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) v) →
                              @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 616) (instOfNatNat (nat_lit 616))))
                                (DecrAlmostLinearSSSP.Decremental.labels b state
                                  (@Subtype.val.{1} (Fin b.input.n) (fun v => @Ne.{1} (Fin b.input.n) v b.input.source)
                                    v))) →
                          ∃ cost t,
                            And
                              (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                DecrAlmostLinearSSSP.Decremental.CoreCommit.headCode s cost t)
                              (And
                                (@LE.le.{0} Nat instLENat cost
                                  (@OfNat.ofNat.{0} Nat (nat_lit 61) (instOfNatNat (nat_lit 61))))
                                (And
                                  (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                                    (DecrAlmostLinearSSSP.Decremental.refresh b state e) t)
                                  (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                                    (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g t)))) ∧ ((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 ξ h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (ctx :
    DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context b B N
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
      impl K0 ξ h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
          @DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
              (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) state
              (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                  impl K0 ξ h Γ init s ctx)) →
            ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b) (xs : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)),
              @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                  (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
                  (@List.cons.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) e xs) →
                @DecrAlmostLinearSSSP.Decremental.Physical.Valid b.input.n
                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                    (@DecrAlmostLinearSSSP.Decremental.indexedPhysical b state
                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b))
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))) →
                  DecrAlmostLinearSSSP.Decremental.RefreshValidity b state e →
                    DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K
                        (DecrAlmostLinearSSSP.Decremental.refresh b state e) →
                      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                          (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e) →
                        ∃ cost t next,
                          And
                            (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                              (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.refreshCode N impl.program) s cost t)
                            (And
                              (@LE.le.{0} Nat instLENat cost
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              b.input.size)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                b.weightExponent)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                            impl K0 ξ h Γ init t next).work
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              b.input.size)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                b.weightExponent)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                            impl K0 ξ h Γ init s ctx).work))
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) N))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 218) (instOfNatNat (nat_lit 218)))))
                              (And
                                (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                                  (DecrAlmostLinearSSSP.Decremental.refresh b state e) t)
                                (And
                                  (DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K
                                    (DecrAlmostLinearSSSP.Decremental.refresh b state e))
                                  (And
                                    (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                                      (DecrAlmostLinearSSSP.Decremental.refresh b state e)
                                      (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init t next)))
                                    (And
                                      (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init t next)
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init s ctx))
                                      (And
                                        (@Eq.{1}
                                          (List.{0}
                                            (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              b.input.size)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                b.weightExponent)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                            impl K0 ξ h Γ init t next)
                                          (@HAppend.hAppend.{0, 0, 0}
                                            (List.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                            (List.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                            (List.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                            (@instHAppendOfAppend.{0}
                                              (List.{0}
                                                (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                              (@List.instAppend.{0}
                                                (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0 ξ h Γ init s ctx)
                                            (@List.cons.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                              (@DecrAlmostLinearSSSP.Decremental.CutOp.queryY b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                (DecrAlmostLinearSSSP.Decremental.tail b e))
                                              (@List.cons.{0}
                                                (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                (@DecrAlmostLinearSSSP.Decremental.CutOp.queryY b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                  (DecrAlmostLinearSSSP.Decremental.head b e))
                                                (@List.cons.{0}
                                                  (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                  (@DecrAlmostLinearSSSP.Decremental.CutOp.erase b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
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
                                                        (@Equiv.instEquivLike.{1, 1}
                                                          (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                          (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) e))
                                                  (@List.cons.{0}
                                                    (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                    (@DecrAlmostLinearSSSP.Decremental.CutOp.insert b.input.n
                                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
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
                                                          (@Equiv.instEquivLike.{1, 1}
                                                            (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                            (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                                        (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) e)
                                                      (DecrAlmostLinearSSSP.Decremental.tail b e)
                                                      (DecrAlmostLinearSSSP.Decremental.head b e)
                                                      (DecrAlmostLinearSSSP.Decremental.capacity b
                                                        (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                                                        (DecrAlmostLinearSSSP.Decremental.labels b state) e))
                                                    (@List.cons.{0}
                                                      (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                      (@DecrAlmostLinearSSSP.Decremental.CutOp.paired b.input.n
                                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                        (DecrAlmostLinearSSSP.Decremental.head b e)
                                                        (DecrAlmostLinearSSSP.Decremental.tail b e)
                                                        (@HSub.hSub.{0, 0, 0} Real Real Real
                                                          (@instHSub.{0} Real Real.instSub)
                                                          (DecrAlmostLinearSSSP.Decremental.capacity b
                                                            (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                                                            (DecrAlmostLinearSSSP.Decremental.labels b state) e)
                                                          (@DecrAlmostLinearSSSP.Decremental.State.cache b state e)))
                                                      (@List.nil.{0}
                                                        (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                          (DecrAlmostLinearSSSP.Decremental.logicalCount b))))))))))
                                        (And
                                          (@LE.le.{0} Nat instLENat
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0 ξ h Γ init s ctx).work
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0 ξ h Γ init t next).work)
                                          (@Eq.{1} Nat
                                            (DecrAlmostLinearSSSP.Decremental.reportVolume
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0 ξ h Γ init t next))
                                            (DecrAlmostLinearSSSP.Decremental.reportVolume
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0 ξ h Γ init s ctx))))))))))) ∧ (∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 ξ h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (ctx :
    DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context b B N
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
      impl K0 ξ h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
            DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K state →
              @DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) state
                  (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                      impl K0 ξ h Γ init s ctx)) →
                ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b)
                  (xs : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)),
                  @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                      (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
                      (@List.cons.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) e xs) →
                    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                        (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e) →
                      ∃ cost t next,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.refreshCode N impl.program) s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init t next).work
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init s ctx).work))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) N))
                                (@OfNat.ofNat.{0} Nat (nat_lit 218) (instOfNatNat (nat_lit 218)))))
                            (And
                              (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                                (DecrAlmostLinearSSSP.Decremental.refresh b state e) t)
                              (And
                                (DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K
                                  (DecrAlmostLinearSSSP.Decremental.refresh b state e))
                                (And
                                  (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                                    (DecrAlmostLinearSSSP.Decremental.refresh b state e)
                                    (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                            b.weightExponent)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                        impl K0 ξ h Γ init t next)))
                                  (And
                                    (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                            b.weightExponent)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                        impl K0 ξ h Γ init t next)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                            b.weightExponent)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                        impl K0 ξ h Γ init s ctx))
                                    (And
                                      (@Eq.{1}
                                        (List.{0}
                                          (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init t next)
                                        (@HAppend.hAppend.{0, 0, 0}
                                          (List.{0}
                                            (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                          (List.{0}
                                            (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                          (List.{0}
                                            (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                          (@instHAppendOfAppend.{0}
                                            (List.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                            (@List.instAppend.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                              b.input.size)
                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                b.weightExponent)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                            impl K0 ξ h Γ init s ctx)
                                          (@List.cons.{0}
                                            (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                            (@DecrAlmostLinearSSSP.Decremental.CutOp.queryY b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                              (DecrAlmostLinearSSSP.Decremental.tail b e))
                                            (@List.cons.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                              (@DecrAlmostLinearSSSP.Decremental.CutOp.queryY b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                (DecrAlmostLinearSSSP.Decremental.head b e))
                                              (@List.cons.{0}
                                                (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                (@DecrAlmostLinearSSSP.Decremental.CutOp.erase b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
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
                                                      (@Equiv.instEquivLike.{1, 1}
                                                        (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                                    (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) e))
                                                (@List.cons.{0}
                                                  (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                  (@DecrAlmostLinearSSSP.Decremental.CutOp.insert b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
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
                                                        (@Equiv.instEquivLike.{1, 1}
                                                          (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                          (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                                      (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) e)
                                                    (DecrAlmostLinearSSSP.Decremental.tail b e)
                                                    (DecrAlmostLinearSSSP.Decremental.head b e)
                                                    (DecrAlmostLinearSSSP.Decremental.capacity b
                                                      (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                                                      (DecrAlmostLinearSSSP.Decremental.labels b state) e))
                                                  (@List.cons.{0}
                                                    (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                    (@DecrAlmostLinearSSSP.Decremental.CutOp.paired b.input.n
                                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                      (DecrAlmostLinearSSSP.Decremental.head b e)
                                                      (DecrAlmostLinearSSSP.Decremental.tail b e)
                                                      (@HSub.hSub.{0, 0, 0} Real Real Real
                                                        (@instHSub.{0} Real Real.instSub)
                                                        (DecrAlmostLinearSSSP.Decremental.capacity b
                                                          (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                                                          (DecrAlmostLinearSSSP.Decremental.labels b state) e)
                                                        (@DecrAlmostLinearSSSP.Decremental.State.cache b state e)))
                                                    (@List.nil.{0}
                                                      (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b))))))))))
                                      (And
                                        (@LE.le.{0} Nat instLENat
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0 ξ h Γ init s ctx).work
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0 ξ h Γ init t next).work)
                                        (@Eq.{1} Nat
                                          (DecrAlmostLinearSSSP.Decremental.reportVolume
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0 ξ h Γ init t next))
                                          (DecrAlmostLinearSSSP.Decremental.reportVolume
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0 ξ h Γ init s ctx)))))))))))))) ∧ (((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.code s
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
    (DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.result s)) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
    DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.code k)) ∧ ((∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.code k) ∧ ((DecrAlmostLinearSSSP.Decremental.Structured.NoMemory DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.code) ∧ (@Eq.{1} Bool
  (DecrAlmostLinearSSSP.Decremental.Structured.evenRegisters DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.code)
  Bool.true))))))) ∧ ((((((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B N : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (e : DecrAlmostLinearSSSP.Decremental.Edge b) (xs : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
  (g : DecrAlmostLinearSSSP.Decremental.Machine) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.CoreSource.Image B (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N
        g s →
      @LE.le.{0} Nat instLENat b.input.n B →
        @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
            (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
            (@List.cons.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) e xs) →
          And
            (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state
              (DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.result s))
            (And
              (DecrAlmostLinearSSSP.Decremental.CoreSource.Image B
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.sourceRecord b B) N g
                (DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.result s))
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.CoreHeadSelect.result s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
                (DecrAlmostLinearSSSP.Decremental.CoreMemory.encodedEdge b e)))) ∧ (∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 ξ h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (ctx :
    DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context b B N
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
      impl K0 ξ h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
          @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) K →
            DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K state →
              @DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) state
                  (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                      impl K0 ξ h Γ init s ctx)) →
                ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b)
                  (xs : List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)),
                  @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                      (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
                      (@List.cons.{0} (DecrAlmostLinearSSSP.Decremental.Edge b) e xs) →
                    @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b state) Bool.false →
                      ∃ cost t next,
                        And
                          (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                            (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.drainOneCode N impl.program) s cost t)
                          (And
                            (@LE.le.{0} Nat instLENat cost
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init t next).work
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init s ctx).work))
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) N))
                                (@OfNat.ofNat.{0} Nat (nat_lit 219) (instOfNatNat (nat_lit 219)))))
                            (And
                              (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                                (DecrAlmostLinearSSSP.Decremental.refresh b state e) t)
                              (And
                                (DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K
                                  (DecrAlmostLinearSSSP.Decremental.refresh b state e))
                                (And
                                  (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                                    (DecrAlmostLinearSSSP.Decremental.refresh b state e)
                                    (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                            b.weightExponent)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                        impl K0 ξ h Γ init t next)))
                                  (And
                                    (DecrAlmostLinearSSSP.Decremental.RuntimeRepairStep b K state
                                      (DecrAlmostLinearSSSP.Decremental.refresh b state e))
                                    (And
                                      (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init t next)
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                              b.weightExponent)
                                            (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                          impl K0 ξ h Γ init s ctx))
                                      (And
                                        (@Eq.{1} Nat
                                          (@List.length.{0}
                                            (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0 ξ h Γ init t next))
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@List.length.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0 ξ h Γ init s ctx))
                                            (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))))
                                        (And
                                          (@Eq.{1} Nat
                                            (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0 ξ h Γ init t next))
                                            (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0 ξ h Γ init s ctx)))
                                          (And
                                            (@LE.le.{0} Nat instLENat
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    b.input.size)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                      b.weightExponent)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                  impl K0 ξ h Γ init s ctx).work
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    b.input.size)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                      b.weightExponent)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                  impl K0 ξ h Γ init t next).work)
                                            (@Eq.{1} Nat
                                              (DecrAlmostLinearSSSP.Decremental.reportVolume
                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    b.input.size)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                      b.weightExponent)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                  impl K0 ξ h Γ init t next))
                                              (DecrAlmostLinearSSSP.Decremental.reportVolume
                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    b.input.size)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                      b.weightExponent)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                  impl K0 ξ h Γ init s ctx)))))))))))))) ∧ ((DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreCommit.headCode
  (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650)))) ∧ (∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.refreshCode N p)
    (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650)))))) ∧ (((∀ (N : Nat) (p : DecrAlmostLinearSSSP.Decremental.Program),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.drainOneCode N p)
    (@OfNat.ofNat.{0} Nat (nat_lit 650) (instOfNatNat (nat_lit 650)))) ∧ (∀ {l : Nat} (xs : List.{0} (Fin l)) (v : Nat) (e : Fin l),
  Iff
    (@Membership.mem.{0, 0} (Fin l) (List.{0} (Fin l)) (@List.instMembership.{0} (Fin l))
      (DecrAlmostLinearSSSP.Decremental.CoreReports.push l xs v) e)
    (Or (@Membership.mem.{0, 0} (Fin l) (List.{0} (Fin l)) (@List.instMembership.{0} (Fin l)) xs e)
      (@Eq.{1} Nat (@Fin.val l e) v)))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReports.fetchCode s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.CoreReports.fetched s)) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 584) (instOfNatNat (nat_lit 584))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreReports.fetchCode k) ∧ (∀ (k : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreReports.fetchCode k))))) ∧ ((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CoreReports.fetched s).natMem s.natMem)
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CoreReports.fetched s).realMem s.realMem)) ∧ (∀ (B offset v : Nat) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))) B →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14))))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) offset) →
        @Eq.{1} Nat
            (s.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) offset))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v) →
          @Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.CoreReports.fetched s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v))) ∧ ((∀ {B l : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B l s →
    (∀ (k : Nat),
        @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
            (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 74) (instOfNatNat (nat_lit 74)))
              (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 552) (instOfNatNat (nat_lit 552)))
                (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))
                  (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))
                    (@List.cons.{0} Nat (@OfNat.ofNat.{0} Nat (nat_lit 542) (instOfNatNat (nat_lit 542)))
                      (@List.nil.{0} Nat))))))
            k →
          @Eq.{1} Nat (t.natReg k) (s.natReg k)) →
      DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B l t) ∧ ((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 546) (instOfNatNat (nat_lit 546))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 584) (instOfNatNat (nat_lit 584))) →
          Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))))
              (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 572) (instOfNatNat (nat_lit 572))) k) →
            DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreReports.body k) ∧ (∀ (k : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreReports.body k)))) ∧ (((∀ (B l offset v : Nat) (xs : List.{0} (Fin l)) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B l s →
    @DecrAlmostLinearSSSP.Decremental.CorePending.View l B xs s →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) offset) →
        @Eq.{1} Nat
            (s.natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) offset))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) v) →
          ∃ cost t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReports.body s cost
                t)
              (And (@LE.le.{0} Nat instLENat cost (@OfNat.ofNat.{0} Nat (nat_lit 16) (instOfNatNat (nat_lit 16))))
                (And
                  (@DecrAlmostLinearSSSP.Decremental.CorePending.View l B
                    (DecrAlmostLinearSSSP.Decremental.CoreReports.push l xs v) t)
                  (And (DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B l t)
                    (And
                      (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))))
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                      (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                        (And
                          (∀ (j : Nat),
                            @Eq.{1} Nat
                              (t.natMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                              (s.natMem
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                          (DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t)))))))) ∧ (∀ {l : Nat} (xs : List.{0} (Fin l)) (reports : List.{0} Nat) (e : Fin l),
  Iff
    (@Membership.mem.{0, 0} (Fin l) (List.{0} (Fin l)) (@List.instMembership.{0} (Fin l))
      (DecrAlmostLinearSSSP.Decremental.CoreReports.consume l xs reports) e)
    (Or (@Membership.mem.{0, 0} (Fin l) (List.{0} (Fin l)) (@List.instMembership.{0} (Fin l)) xs e)
      (@Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) reports (@Fin.val l e))))) ∧ ((∀ (B l : Nat) (reports : List.{0} Nat) (xs : List.{0} (Fin l)) (offset : Nat)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B l s →
    @DecrAlmostLinearSSSP.Decremental.CorePending.View l B xs s →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))))
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) offset) →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 582) (instOfNatNat (nat_lit 582))))
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset (@List.length.{0} Nat reports))) →
          (∀ (j : Nat) (hj : @LT.lt.{0} Nat instLTNat j (@List.length.{0} Nat reports)),
              @Eq.{1} Nat
                (s.natMem
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset j)))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@GetElem.getElem.{0, 0, 0} (List.{0} Nat) Nat Nat
                    (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{0} Nat as))
                    (@List.instGetElemNatLtLength.{0} Nat) reports j hj))) →
            ∃ cost t,
              And
                (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReports.loop s
                  cost t)
                (And
                  (@LE.le.{0} Nat instLENat cost
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18))) (@List.length.{0} Nat reports))
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (And
                    (@DecrAlmostLinearSSSP.Decremental.CorePending.View l B
                      (DecrAlmostLinearSSSP.Decremental.CoreReports.consume l xs reports) t)
                    (And (DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B l t)
                      (And
                        (@Eq.{1} Nat (t.natReg (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))))
                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) offset
                              (@List.length.{0} Nat reports))))
                        (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                          (And
                            (∀ (j : Nat),
                              @Eq.{1} Nat
                                (t.natMem
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                (s.natMem
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                            (DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t)))))))) ∧ ((∀ {l : Nat} (g : DecrAlmostLinearSSSP.Decremental.Machine) (e : Fin l),
  Iff
    (@Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat)
      (DecrAlmostLinearSSSP.Decremental.CoreReports.reportList g) (@Fin.val l e))
    (@DecrAlmostLinearSSSP.Decremental.Reported l g e)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReports.setup s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.CoreReports.setupData s))))))) ∧ (((((∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 582) (instOfNatNat (nat_lit 582))) →
      DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreReports.setup k) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    And
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CoreReports.setupData s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))))
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
      (@Eq.{1} Nat
        ((DecrAlmostLinearSSSP.Decremental.CoreReports.setupData s).natReg
          (@OfNat.ofNat.{0} Nat (nat_lit 582) (instOfNatNat (nat_lit 582))))
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 23) (instOfNatNat (nat_lit 23))))))) ∧ ((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  And (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.CoreReports.setupData s).natMem s.natMem)
    (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.CoreReports.setupData s).realMem s.realMem)) ∧ (∀ (B l : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine) (xs : List.{0} (Fin l))
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B l s →
    @DecrAlmostLinearSSSP.Decremental.CorePending.View l B xs s →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        DecrAlmostLinearSSSP.Decremental.ShadowDataRep B (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) s
            g →
          ∃ cost t,
            And
              (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReports.code s cost
                t)
              (And
                (@LE.le.{0} Nat instLENat cost
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                      (DecrAlmostLinearSSSP.Decremental.reportCount g))
                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
                (And
                  (@DecrAlmostLinearSSSP.Decremental.CorePending.View l B
                    (DecrAlmostLinearSSSP.Decremental.CoreReports.consume l xs
                      (DecrAlmostLinearSSSP.Decremental.CoreReports.reportList g))
                    t)
                  (And (DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B l t)
                    (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                      (And
                        (∀ (j : Nat),
                          @Eq.{1} Nat
                            (t.natMem
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                            (s.natMem
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) j))
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                        (And
                          (∀ (e : Fin l),
                            Iff
                              (@Membership.mem.{0, 0} (Fin l) (List.{0} (Fin l)) (@List.instMembership.{0} (Fin l))
                                (DecrAlmostLinearSSSP.Decremental.CoreReports.consume l xs
                                  (DecrAlmostLinearSSSP.Decremental.CoreReports.reportList g))
                                e)
                              (Or
                                (@Membership.mem.{0, 0} (Fin l) (List.{0} (Fin l)) (@List.instMembership.{0} (Fin l)) xs
                                  e)
                                (@DecrAlmostLinearSSSP.Decremental.Reported l g e)))
                          (DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t)))))))))) ∧ (((∀ (l : Nat) (xs : List.{0} (Fin l)) (v : Nat),
  @LE.le.{0} Nat instLENat (@List.length.{0} (Fin l) (DecrAlmostLinearSSSP.Decremental.CoreReports.push l xs v))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin l) xs)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))) ∧ (∀ (l : Nat) (xs : List.{0} (Fin l)) (reports : List.{0} Nat),
  @LE.le.{0} Nat instLENat
    (@List.length.{0} (Fin l) (DecrAlmostLinearSSSP.Decremental.CoreReports.consume l xs reports))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (@List.length.{0} (Fin l) xs)
      (@List.length.{0} Nat reports)))) ∧ ((∀ (l : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine),
  @LE.le.{0} Nat instLENat
    (@List.length.{0} (Fin l)
      (DecrAlmostLinearSSSP.Decremental.CoreReports.consume l (@List.nil.{0} (Fin l))
        (DecrAlmostLinearSSSP.Decremental.CoreReports.reportList g)))
    (DecrAlmostLinearSSSP.Decremental.reportCount g)) ∧ ((∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N m exponent : Nat} {K K0 ξ h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (ctx : DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context b B N m exponent impl K0 ξ h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
          @DecrAlmostLinearSSSP.Decremental.Physical.Valid b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
              (@DecrAlmostLinearSSSP.Decremental.CutState.physical b.input.n
                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent impl K0 ξ h Γ init s
                    ctx)))
              m exponent →
            @DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) state
                (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent impl K0 ξ h Γ init s
                    ctx)) →
              @Ne.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                  (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
                    (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
                      (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero))) →
                @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                    K0 →
                  @LE.le.{0} Real Real.instLE K0 K →
                    ∃ cost t next,
                      And
                        (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                          (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.ratioCode N impl.program) s cost t)
                        (And
                          (@LE.le.{0} Nat instLENat cost
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent
                                        impl K0 ξ h Γ init t next).work
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent
                                        impl K0 ξ h Γ init s ctx).work))
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N))
                              (@OfNat.ofNat.{0} Nat (nat_lit 19) (instOfNatNat (nat_lit 19)))))
                          (And (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state t)
                            (And
                              (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) state
                                (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent impl
                                    K0 ξ h Γ init t next)))
                              (And
                                (@DecrAlmostLinearSSSP.Decremental.RatioGuarantee b.input.n
                                  (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                    (@instFintypeSum.{0, 0} (Fin b.input.k)
                                      (DecrAlmostLinearSSSP.Decremental.ReturnVertex b) (Fin.fintype b.input.k)
                                      (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
                                  (DecrAlmostLinearSSSP.Decremental.cachedPhysical b state) K
                                  (@DecrAlmostLinearSSSP.Decremental.CutState.lastG b.input.n
                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent
                                        impl K0 ξ h Γ init t next)))
                                  (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n
                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent
                                        impl K0 ξ h Γ init t next)))
                                  (@DecrAlmostLinearSSSP.Decremental.CutState.lastCut b.input.n
                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m exponent
                                        impl K0 ξ h Γ init t next))))
                                (And
                                  (@Eq.{1} Bool
                                    (@DecrAlmostLinearSSSP.Decremental.CutState.hasCut b.input.n
                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                      (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                          exponent impl K0 ξ h Γ init t next)))
                                    Bool.true)
                                  (And
                                    (@Eq.{1} Real
                                      (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 29) (instOfNatNat (nat_lit 29))))
                                      (@DecrAlmostLinearSSSP.Decremental.CutState.lastG b.input.n
                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                        (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                            exponent impl K0 ξ h Γ init t next))))
                                    (And
                                      (@Eq.{1} Real
                                        (t.realReg (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31))))
                                        (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n
                                          (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                          (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                              exponent impl K0 ξ h Γ init t next))))
                                      (And
                                        (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N m
                                            exponent impl K0 ξ h Γ init t next)
                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N m
                                            exponent impl K0 ξ h Γ init s ctx))
                                        (And
                                          (@Eq.{1}
                                            (List.{0}
                                              (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N m
                                              exponent impl K0 ξ h Γ init t next)
                                            (@HAppend.hAppend.{0, 0, 0}
                                              (List.{0}
                                                (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                              (List.{0}
                                                (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                              (List.{0}
                                                (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                              (@instHAppendOfAppend.{0}
                                                (List.{0}
                                                  (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
                                                (@List.instAppend.{0}
                                                  (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b))))
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N m
                                                exponent impl K0 ξ h Γ init s ctx)
                                              (@List.cons.{0}
                                                (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                (@DecrAlmostLinearSSSP.Decremental.CutOp.ratio b.input.n
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                (@List.nil.{0}
                                                  (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                    (DecrAlmostLinearSSSP.Decremental.logicalCount b))))))
                                          (And
                                            (@LE.le.{0} Nat instLENat
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                                  exponent impl K0 ξ h Γ init s ctx).work
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N m
                                                  exponent impl K0 ξ h Γ init t next).work)
                                            (@Eq.{1} Nat
                                              (DecrAlmostLinearSSSP.Decremental.reportVolume
                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                                  m exponent impl K0 ξ h Γ init t next))
                                              (DecrAlmostLinearSSSP.Decremental.reportVolume
                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines b B N
                                                  m exponent impl K0 ξ h Γ init s ctx)))))))))))))) ∧ (∀ (k : Nat),
  @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 546) (instOfNatNat (nat_lit 546))) →
    @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 560) (instOfNatNat (nat_lit 560))) →
      @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 580) (instOfNatNat (nat_lit 580))) →
        @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 582) (instOfNatNat (nat_lit 582))) →
          @Ne.{1} Nat k (@OfNat.ofNat.{0} Nat (nat_lit 584) (instOfNatNat (nat_lit 584))) →
            Or (@LT.lt.{0} Nat instLTNat k (@OfNat.ofNat.{0} Nat (nat_lit 562) (instOfNatNat (nat_lit 562))))
                (@LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 572) (instOfNatNat (nat_lit 572))) k) →
              DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreReports.code k))))) ∧ ((((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.CoreReports.code
    (DecrAlmostLinearSSSP.Decremental.shadowReg j)) ∧ (∀ (j : Nat), DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.CoreReports.code j)) ∧ ((∀ {B l : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t →
    ∀ (j : Nat),
      @LE.le.{0} Nat instLENat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) l))
          j →
        @Eq.{1} Nat (t.natMem j) (s.natMem j)) ∧ ((∀ {B l : Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t →
    ∀ (j : Nat), @LE.le.{0} Nat instLENat j B → @Eq.{1} Nat (t.natMem j) (s.natMem j)) ∧ (∀ {B : Nat} (b : DecrAlmostLinearSSSP.Decremental.Core) {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B (DecrAlmostLinearSSSP.Decremental.logicalCount b) s t →
    ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b) (offset : Nat),
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) offset →
        @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5))) →
          @Eq.{1} Nat (t.natMem (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e offset))
            (s.natMem (DecrAlmostLinearSSSP.Decremental.CoreMemory.field b B e offset)))))) ∧ (((∀ (B R N l : Nat) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (cost : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g s →
    @LE.le.{0} Nat instLENat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) l))
        R →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReports.code s cost t →
        @Eq.{1} (Nat → Real) t.realMem s.realMem →
          DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B l s t →
            DecrAlmostLinearSSSP.Decremental.CoreSource.Image B R N g t) ∧ (∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (ys : List.{0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
  (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data) (cost : Nat),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.CoreReports.code s cost t →
        @DecrAlmostLinearSSSP.Decremental.CorePending.View (DecrAlmostLinearSSSP.Decremental.logicalCount b) B ys t →
          @Eq.{1} (Nat → Real) t.realMem s.realMem →
            DecrAlmostLinearSSSP.Decremental.CorePending.MemoryFrame B (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                s t →
              DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                (@DecrAlmostLinearSSSP.Decremental.State.mk b (@DecrAlmostLinearSSSP.Decremental.State.active b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.y b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.cache b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.baseline b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.nonzeroEntries b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.sample b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.output b state)
                  (@List.map.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                    (DecrAlmostLinearSSSP.Decremental.Edge b)
                    (@DFunLike.coe.{1, 1, 1}
                      (Equiv.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                        (DecrAlmostLinearSSSP.Decremental.Edge b))
                      (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                      (fun x => DecrAlmostLinearSSSP.Decremental.Edge b)
                      (@EquivLike.toFunLike.{1, 1, 1}
                        (Equiv.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                          (DecrAlmostLinearSSSP.Decremental.Edge b))
                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                        (DecrAlmostLinearSSSP.Decremental.Edge b)
                        (@Equiv.instEquivLike.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                          (DecrAlmostLinearSSSP.Decremental.Edge b)))
                      (@Equiv.symm.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                        (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                        (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)))
                    ys)
                  (@DecrAlmostLinearSSSP.Decremental.State.stopped b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.toggles b state)
                  (@DecrAlmostLinearSSSP.Decremental.State.history b state))
                t)) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (B : Nat) (K : Real) (state : DecrAlmostLinearSSSP.Decremental.State b)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    DecrAlmostLinearSSSP.Decremental.CoreReports.Environment B (DecrAlmostLinearSSSP.Decremental.logicalCount b) s) ∧ ((∀ (b : DecrAlmostLinearSSSP.Decremental.Core) (g : DecrAlmostLinearSSSP.Decremental.Machine)
  (ys : List.{0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))),
  (∀ (d : Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)),
      Iff
        (@Membership.mem.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
          (List.{0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)))
          (@List.instMembership.{0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))) ys d)
        (@DecrAlmostLinearSSSP.Decremental.Reported (DecrAlmostLinearSSSP.Decremental.logicalCount b) g d)) →
    ∀ (e : DecrAlmostLinearSSSP.Decremental.Edge b),
      Iff
        (@Membership.mem.{0, 0} (DecrAlmostLinearSSSP.Decremental.Edge b)
          (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
          (@List.instMembership.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
          (@List.map.{0, 0} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
            (DecrAlmostLinearSSSP.Decremental.Edge b)
            (@DFunLike.coe.{1, 1, 1}
              (Equiv.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                (DecrAlmostLinearSSSP.Decremental.Edge b))
              (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)) (fun x => DecrAlmostLinearSSSP.Decremental.Edge b)
              (@EquivLike.toFunLike.{1, 1, 1}
                (Equiv.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                  (DecrAlmostLinearSSSP.Decremental.Edge b))
                (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b)) (DecrAlmostLinearSSSP.Decremental.Edge b)
                (@Equiv.instEquivLike.{1, 1} (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                  (DecrAlmostLinearSSSP.Decremental.Edge b)))
              (@Equiv.symm.{1, 1} (DecrAlmostLinearSSSP.Decremental.Edge b)
                (Fin (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)))
            ys)
          e)
        (@DecrAlmostLinearSSSP.Decremental.Reported (DecrAlmostLinearSSSP.Decremental.logicalCount b) g
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
            (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) e))) ∧ (∀ {b : DecrAlmostLinearSSSP.Decremental.Core} {B N : Nat} {K K0 h Γ init : Real}
  {impl : DecrAlmostLinearSSSP.Decremental.CutImplementation} {state : DecrAlmostLinearSSSP.Decremental.State b}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data}
  (ctx :
    DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context b B N
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
      impl K0
      (@HPow.hPow.{0, 0, 0} Real Int Real
        (@instHPow.{0, 0} Real Int (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid))) K
        (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
      h Γ init s),
  DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K state s →
    @LE.le.{0} Nat instLENat b.input.n B →
      @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))) N →
        @LE.le.{0} Nat instLENat (DecrAlmostLinearSSSP.Decremental.registerBound impl.program.code) N →
          @LE.le.{0} Real Real.instLE
              (@OfNat.ofNat.{0} Real (nat_lit 32)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 32) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))
              K →
            DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K state →
              @DecrAlmostLinearSSSP.Decremental.CutModel b (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                  (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b) state
                  (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                      impl K0
                      (@HPow.hPow.{0, 0, 0} Real Int Real
                        (@instHPow.{0, 0} Real Int
                          (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                        K (@Neg.neg.{0} Int Int.instNegInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                      h Γ init s ctx)) →
                @Eq.{1} Bool (@DecrAlmostLinearSSSP.Decremental.State.stopped b state) Bool.false →
                  @Eq.{1} (List.{0} (DecrAlmostLinearSSSP.Decremental.Edge b))
                      (@DecrAlmostLinearSSSP.Decremental.State.pending b state)
                      (@List.nil.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)) →
                    @Ne.{1} (Fin b.input.n → Real) (@DecrAlmostLinearSSSP.Decremental.State.cachedGradient b state)
                        (@OfNat.ofNat.{0} (Fin b.input.n → Real) (nat_lit 0)
                          (@Zero.toOfNat0.{0} (Fin b.input.n → Real)
                            (@Pi.instZero.{0, 0} (Fin b.input.n) (fun a => Real) fun i => Real.instZero))) →
                      @Eq.{1} Bool
                          (@DecrAlmostLinearSSSP.Decremental.CutState.hasCut b.input.n
                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                            (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                impl K0
                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                  (@instHPow.{0, 0} Real Int
                                    (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                  K
                                  (@Neg.neg.{0} Int Int.instNegInt
                                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                h Γ init s ctx)))
                          Bool.true →
                        @DecrAlmostLinearSSSP.Decremental.RatioGuarantee b.input.n
                            (@Fintype.card.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                              (@instFintypeSum.{0, 0} (Fin b.input.k) (DecrAlmostLinearSSSP.Decremental.ReturnVertex b)
                                (Fin.fintype b.input.k) (DecrAlmostLinearSSSP.Decremental.instFintypeReturnVertex b)))
                            (DecrAlmostLinearSSSP.Decremental.cachedPhysical b state) K
                            (@DecrAlmostLinearSSSP.Decremental.CutState.lastG b.input.n
                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                              (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                  impl K0
                                  (@HPow.hPow.{0, 0, 0} Real Int Real
                                    (@instHPow.{0, 0} Real Int
                                      (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                    K
                                    (@Neg.neg.{0} Int Int.instNegInt
                                      (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                  h Γ init s ctx)))
                            (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n
                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                              (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                  impl K0
                                  (@HPow.hPow.{0, 0, 0} Real Int Real
                                    (@instHPow.{0, 0} Real Int
                                      (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                    K
                                    (@Neg.neg.{0} Int Int.instNegInt
                                      (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                  h Γ init s ctx)))
                            (@DecrAlmostLinearSSSP.Decremental.CutState.lastCut b.input.n
                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                              (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) b.weightExponent)
                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                  impl K0
                                  (@HPow.hPow.{0, 0, 0} Real Int Real
                                    (@instHPow.{0, 0} Real Int
                                      (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                    K
                                    (@Neg.neg.{0} Int Int.instNegInt
                                      (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                  h Γ init s ctx))) →
                          @LT.lt.{0} Real Real.instLT
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@DecrAlmostLinearSSSP.Decremental.CutState.lastG b.input.n
                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                  (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                          b.weightExponent)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                      impl K0
                                      (@HPow.hPow.{0, 0, 0} Real Int Real
                                        (@instHPow.{0, 0} Real Int
                                          (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                        K
                                        (@Neg.neg.{0} Int Int.instNegInt
                                          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                      h Γ init s ctx)))
                                (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n
                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                  (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                          b.weightExponent)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                      impl K0
                                      (@HPow.hPow.{0, 0, 0} Real Int Real
                                        (@instHPow.{0, 0} Real Int
                                          (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                        K
                                        (@Neg.neg.{0} Int Int.instNegInt
                                          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                      h Γ init s ctx))))
                              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                                (@Neg.neg.{0} Real Real.instNeg
                                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                  (@OfNat.ofNat.{0} Real (nat_lit 4)
                                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                      (@Nat.instAtLeastTwoHAddOfNat
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                        (@Nat.instNeZeroSucc
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                                  K)) →
                            @Eq.{1} Real (s.realReg (@OfNat.ofNat.{0} Nat (nat_lit 31) (instOfNatNat (nat_lit 31))))
                                (@DecrAlmostLinearSSSP.Decremental.CutState.lastU b.input.n
                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                  (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) b.input.size)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                          b.weightExponent)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                      impl K0
                                      (@HPow.hPow.{0, 0, 0} Real Int Real
                                        (@instHPow.{0, 0} Real Int
                                          (@ZPow.toPow.{0} Real (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                        K
                                        (@Neg.neg.{0} Int Int.instNegInt
                                          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                      h Γ init s ctx))) →
                              ∃ cost t next reports,
                                And
                                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                                    (DecrAlmostLinearSSSP.Decremental.CoreNativeCut.toggleCode N impl.program) s cost t)
                                  (And
                                    (@LE.le.{0} Nat instLENat cost
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (DecrAlmostLinearSSSP.Decremental.dispatchCharge impl.program.code)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                              (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      b.input.size)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b.weightExponent)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                    impl K0
                                                    (@HPow.hPow.{0, 0, 0} Real Int Real
                                                      (@instHPow.{0, 0} Real Int
                                                        (@ZPow.toPow.{0} Real
                                                          (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                      K
                                                      (@Neg.neg.{0} Int Int.instNegInt
                                                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                    h Γ init t next).work
                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      b.input.size)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b.weightExponent)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                    impl K0
                                                    (@HPow.hPow.{0, 0, 0} Real Int Real
                                                      (@instHPow.{0, 0} Real Int
                                                        (@ZPow.toPow.{0} Real
                                                          (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                      K
                                                      (@Neg.neg.{0} Int Int.instNegInt
                                                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                    h Γ init s ctx).work))
                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                              (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))) N))
                                          (@OfNat.ofNat.{0} Nat (nat_lit 27) (instOfNatNat (nat_lit 27))))
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))
                                          (DecrAlmostLinearSSSP.Decremental.reportCount
                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                b.input.size)
                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                  b.weightExponent)
                                                (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                              impl K0
                                              (@HPow.hPow.{0, 0, 0} Real Int Real
                                                (@instHPow.{0, 0} Real Int
                                                  (@ZPow.toPow.{0} Real
                                                    (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                K
                                                (@Neg.neg.{0} Int Int.instNegInt
                                                  (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                              h Γ init t next)))))
                                    (And
                                      (DecrAlmostLinearSSSP.Decremental.CoreHost.Image b B K
                                        (DecrAlmostLinearSSSP.Decremental.reportedToggle b K state
                                          (@DecrAlmostLinearSSSP.Decremental.modelReply b
                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                            (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0
                                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                                  (@instHPow.{0, 0} Real Int
                                                    (@ZPow.toPow.{0} Real
                                                      (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                  K
                                                  (@Neg.neg.{0} Int Int.instNegInt
                                                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                h Γ init s ctx)))
                                          reports)
                                        t)
                                      (And
                                        (DecrAlmostLinearSSSP.Decremental.RuntimeBounds b K
                                          (DecrAlmostLinearSSSP.Decremental.reportedToggle b K state
                                            (@DecrAlmostLinearSSSP.Decremental.modelReply b
                                              (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                              (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    b.input.size)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                      b.weightExponent)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                  impl K0
                                                  (@HPow.hPow.{0, 0, 0} Real Int Real
                                                    (@instHPow.{0, 0} Real Int
                                                      (@ZPow.toPow.{0} Real
                                                        (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                    K
                                                    (@Neg.neg.{0} Int Int.instNegInt
                                                      (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                  h Γ init s ctx)))
                                            reports))
                                        (And
                                          (@DecrAlmostLinearSSSP.Decremental.CutModel b
                                            (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                            (DecrAlmostLinearSSSP.Decremental.logicalIndexEquiv b)
                                            (DecrAlmostLinearSSSP.Decremental.reportedToggle b K state
                                              (@DecrAlmostLinearSSSP.Decremental.modelReply b
                                                (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                  (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                      b.input.size)
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                        b.weightExponent)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                    impl K0
                                                    (@HPow.hPow.{0, 0, 0} Real Int Real
                                                      (@instHPow.{0, 0} Real Int
                                                        (@ZPow.toPow.{0} Real
                                                          (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                      K
                                                      (@Neg.neg.{0} Int Int.instNegInt
                                                        (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                    h Γ init s ctx)))
                                              reports)
                                            (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                              (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B N
                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                  b.input.size)
                                                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                    b.weightExponent)
                                                  (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                impl K0
                                                (@HPow.hPow.{0, 0, 0} Real Int Real
                                                  (@instHPow.{0, 0} Real Int
                                                    (@ZPow.toPow.{0} Real
                                                      (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                  K
                                                  (@Neg.neg.{0} Int Int.instNegInt
                                                    (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                h Γ init t next)))
                                          (And
                                            (DecrAlmostLinearSSSP.Decremental.RuntimeRepairStep b K state
                                              (DecrAlmostLinearSSSP.Decremental.reportedToggle b K state
                                                (@DecrAlmostLinearSSSP.Decremental.modelReply b
                                                  (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                  (impl.view b.input.n (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b B
                                                      N
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                        b.input.size)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b.weightExponent)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                      impl K0
                                                      (@HPow.hPow.{0, 0, 0} Real Int Real
                                                        (@instHPow.{0, 0} Real Int
                                                          (@ZPow.toPow.{0} Real
                                                            (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                        K
                                                        (@Neg.neg.{0} Int Int.instNegInt
                                                          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                      h Γ init s ctx)))
                                                reports))
                                            (And
                                              (@Eq.{1} DecrAlmostLinearSSSP.Decremental.Machine
                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    b.input.size)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                      b.weightExponent)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                  impl K0
                                                  (@HPow.hPow.{0, 0, 0} Real Int Real
                                                    (@instHPow.{0, 0} Real Int
                                                      (@ZPow.toPow.{0} Real
                                                        (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                    K
                                                    (@Neg.neg.{0} Int Int.instNegInt
                                                      (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                  h Γ init t next)
                                                (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.first b B N
                                                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                    b.input.size)
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                      b.weightExponent)
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                  impl K0
                                                  (@HPow.hPow.{0, 0, 0} Real Int Real
                                                    (@instHPow.{0, 0} Real Int
                                                      (@ZPow.toPow.{0} Real
                                                        (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                    K
                                                    (@Neg.neg.{0} Int Int.instNegInt
                                                      (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                  h Γ init s ctx))
                                              (And
                                                (@Eq.{1} Nat
                                                  (@List.length.{0}
                                                    (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                    (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                        b.input.size)
                                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                                          b.weightExponent)
                                                        (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68))))
                                                      impl K0
                                                      (@HPow.hPow.{0, 0, 0} Real Int Real
                                                        (@instHPow.{0, 0} Real Int
                                                          (@ZPow.toPow.{0} Real
                                                            (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                        K
                                                        (@Neg.neg.{0} Int Int.instNegInt
                                                          (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))
                                                      h Γ init t next))
                                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                    (@List.length.{0}
                                                      (DecrAlmostLinearSSSP.Decremental.CutOp b.input.n
                                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b))
                                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          b.input.size)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b.weightExponent)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                            (instOfNatNat (nat_lit 68))))
                                                        impl K0
                                                        (@HPow.hPow.{0, 0, 0} Real Int Real
                                                          (@instHPow.{0, 0} Real Int
                                                            (@ZPow.toPow.{0} Real
                                                              (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                          K
                                                          (@Neg.neg.{0} Int Int.instNegInt
                                                            (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                              (@instOfNat (nat_lit 2)))))
                                                        h Γ init s ctx))
                                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                (And
                                                  (@Eq.{1} Nat
                                                    (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                                      (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B N
                                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                                          b.input.size)
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                              (instOfNatNat (nat_lit 4)))
                                                            b.weightExponent)
                                                          (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                            (instOfNatNat (nat_lit 68))))
                                                        impl K0
                                                        (@HPow.hPow.{0, 0, 0} Real Int Real
                                                          (@instHPow.{0, 0} Real Int
                                                            (@ZPow.toPow.{0} Real
                                                              (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                          K
                                                          (@Neg.neg.{0} Int Int.instNegInt
                                                            (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                              (@instOfNat (nat_lit 2)))))
                                                        h Γ init t next))
                                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                      (@DecrAlmostLinearSSSP.Decremental.toggleVolume b.input.n
                                                        (DecrAlmostLinearSSSP.Decremental.logicalCount b)
                                                        (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.ops b B
                                                          N
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))
                                                            b.input.size)
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b.weightExponent)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                              (instOfNatNat (nat_lit 68))))
                                                          impl K0
                                                          (@HPow.hPow.{0, 0, 0} Real Int Real
                                                            (@instHPow.{0, 0} Real Int
                                                              (@ZPow.toPow.{0} Real
                                                                (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                            K
                                                            (@Neg.neg.{0} Int Int.instNegInt
                                                              (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                (@instOfNat (nat_lit 2)))))
                                                          h Γ init s ctx))
                                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                                  (And
                                                    (@LE.le.{0} Nat instLENat
                                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b
                                                          B N
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))
                                                            b.input.size)
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b.weightExponent)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                              (instOfNatNat (nat_lit 68))))
                                                          impl K0
                                                          (@HPow.hPow.{0, 0, 0} Real Int Real
                                                            (@instHPow.{0, 0} Real Int
                                                              (@ZPow.toPow.{0} Real
                                                                (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                            K
                                                            (@Neg.neg.{0} Int Int.instNegInt
                                                              (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                (@instOfNat (nat_lit 2)))))
                                                          h Γ init s ctx).work
                                                      (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current b
                                                          B N
                                                          (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                            (@instHMul.{0} Nat instMulNat)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                              (instOfNatNat (nat_lit 2)))
                                                            b.input.size)
                                                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                            (@instHAdd.{0} Nat instAddNat)
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                (instOfNatNat (nat_lit 4)))
                                                              b.weightExponent)
                                                            (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                              (instOfNatNat (nat_lit 68))))
                                                          impl K0
                                                          (@HPow.hPow.{0, 0, 0} Real Int Real
                                                            (@instHPow.{0, 0} Real Int
                                                              (@ZPow.toPow.{0} Real
                                                                (@DivInvMonoid.toZPow.{0} Real Real.instDivInvMonoid)))
                                                            K
                                                            (@Neg.neg.{0} Int Int.instNegInt
                                                              (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                (@instOfNat (nat_lit 2)))))
                                                          h Γ init t next).work)
                                                    (And
                                                      (@Eq.{1} Nat
                                                        (DecrAlmostLinearSSSP.Decremental.reportVolume
                                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines
                                                            b B N
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              b.input.size)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b.weightExponent)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                (instOfNatNat (nat_lit 68))))
                                                            impl K0
                                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                                              (@instHPow.{0, 0} Real Int
                                                                (@ZPow.toPow.{0} Real
                                                                  (@DivInvMonoid.toZPow.{0} Real
                                                                    Real.instDivInvMonoid)))
                                                              K
                                                              (@Neg.neg.{0} Int Int.instNegInt
                                                                (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                  (@instOfNat (nat_lit 2)))))
                                                            h Γ init t next))
                                                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                                          (DecrAlmostLinearSSSP.Decremental.reportVolume
                                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.machines
                                                              b B N
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                b.input.size)
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                    (instOfNatNat (nat_lit 4)))
                                                                  b.weightExponent)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                  (instOfNatNat (nat_lit 68))))
                                                              impl K0
                                                              (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                (@instHPow.{0, 0} Real Int
                                                                  (@ZPow.toPow.{0} Real
                                                                    (@DivInvMonoid.toZPow.{0} Real
                                                                      Real.instDivInvMonoid)))
                                                                K
                                                                (@Neg.neg.{0} Int Int.instNegInt
                                                                  (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                    (@instOfNat (nat_lit 2)))))
                                                              h Γ init s ctx))
                                                          (DecrAlmostLinearSSSP.Decremental.reportCount
                                                            (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current
                                                              b B N
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                  (instOfNatNat (nat_lit 2)))
                                                                b.input.size)
                                                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                                (@instHAdd.{0} Nat instAddNat)
                                                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                  (@instHMul.{0} Nat instMulNat)
                                                                  (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                    (instOfNatNat (nat_lit 4)))
                                                                  b.weightExponent)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                  (instOfNatNat (nat_lit 68))))
                                                              impl K0
                                                              (@HPow.hPow.{0, 0, 0} Real Int Real
                                                                (@instHPow.{0, 0} Real Int
                                                                  (@ZPow.toPow.{0} Real
                                                                    (@DivInvMonoid.toZPow.{0} Real
                                                                      Real.instDivInvMonoid)))
                                                                K
                                                                (@Neg.neg.{0} Int Int.instNegInt
                                                                  (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                    (@instOfNat (nat_lit 2)))))
                                                              h Γ init t next))))
                                                      (@LE.le.{0} Nat instLENat
                                                        (@List.length.{0} (DecrAlmostLinearSSSP.Decremental.Edge b)
                                                          reports)
                                                        (DecrAlmostLinearSSSP.Decremental.reportCount
                                                          (@DecrAlmostLinearSSSP.Decremental.CoreNativeCut.Context.current
                                                            b B N
                                                            (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                              (@instHMul.{0} Nat instMulNat)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 2)
                                                                (instOfNatNat (nat_lit 2)))
                                                              b.input.size)
                                                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat
                                                              (@instHAdd.{0} Nat instAddNat)
                                                              (@HMul.hMul.{0, 0, 0} Nat Nat Nat
                                                                (@instHMul.{0} Nat instMulNat)
                                                                (@OfNat.ofNat.{0} Nat (nat_lit 4)
                                                                  (instOfNatNat (nat_lit 4)))
                                                                b.weightExponent)
                                                              (@OfNat.ofNat.{0} Nat (nat_lit 68)
                                                                (instOfNatNat (nat_lit 68))))
                                                            impl K0
                                                            (@HPow.hPow.{0, 0, 0} Real Int Real
                                                              (@instHPow.{0, 0} Real Int
                                                                (@ZPow.toPow.{0} Real
                                                                  (@DivInvMonoid.toZPow.{0} Real
                                                                    Real.instDivInvMonoid)))
                                                              K
                                                              (@Neg.neg.{0} Int Int.instNegInt
                                                                (@OfNat.ofNat.{0} Int (nat_lit 2)
                                                                  (@instOfNat (nat_lit 2)))))
                                                            h Γ init t next))))))))))))))))))))) := by sorry
