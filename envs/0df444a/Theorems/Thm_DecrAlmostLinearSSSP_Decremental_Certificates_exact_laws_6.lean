-- Prove2me | Theorems.Thm_DecrAlmostLinearSSSP_Decremental_Certificates_exact_laws_6
-- name    : DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T11:13:25.401107+00:00
-- url     : https://prove2.me/theorems/dda0a575-c063-4123-a4ed-bff2c7f93ebf
-- title:
--   Label-setting invariants and native adjacency construction
-- statement:
--   This collection gives the universally quantified contracts for label-setting invariants and native adjacency construction. All graph identifiers, queue keys, payloads, registers and addresses are finite natural indices; capacities and arithmetic registers use the scalar RAM types defined in the accompanying interface.
--
--   The label-setting invariant relates settled vertices, tentative labels, witnessing walks and queue coverage. Relaxing an active outgoing edge preserves that invariant, and settling a minimum-label vertex certifies its exact shortest distance. Native adjacency construction preserves distinct edge identifiers, follows the specified linked lists, and initializes activity flags. Tentative and settled memory predicates agree with the corresponding mathematical labels and reachability facts.
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

theorem DecrAlmostLinearSSSP.Decremental.Certificates.exact_laws_6 : (((((((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → ENNReal)
  (u v : Fin n),
  Not (@DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v) →
    @Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.distance n k g active w u v)
      (@Top.top.{0} ENNReal ENNReal.instTop)) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real)
  (B : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) B →
    ∀ (u v : Fin n),
      Not (@DecrAlmostLinearSSSP.Decremental.Reachable n k g active u v) →
        @Eq.{1} Real (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B u v) B)) ∧ ((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real)
  (B c : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) B →
    @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c →
      ∀ (u v : Fin n),
        @Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.distance n k g active (fun e => ENNReal.ofReal (w e)) u v)
            (ENNReal.ofReal c) →
          @Eq.{1} Real (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B u v)
            (@Min.min.{0} Real Real.instMin B c)) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real)
  (B : Real),
  @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) B →
    ∀ (u : Fin n),
      @Eq.{1} Real (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B u u)
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))) ∧ (((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real),
  (∀ (e : Fin k),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w e)) →
    ∀ (B : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) B →
        ∀ (u v : Fin n),
          @LT.lt.{0} Real Real.instLT (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B u v) B →
            ∃ es,
              And (@DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es)
                (@Eq.{1} Real (@List.sum.{0} Real Real.instAdd Real.instZero (@List.map.{0, 0} (Fin k) Real w es))
                  (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B u v))) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real),
  (∀ (e : Fin k),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w e)) →
    ∀ (B : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) B →
        ∀ (t : Fin n) (e : Fin k),
          @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
              (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active e →
            @LE.le.{0} Real Real.instLE
              (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B
                (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) t)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (w e)
                (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B
                  (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e) t)))) ∧ ((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    ∀ (p : Fin n → Real) (w : Fin k → Real),
      (∀ (e : Fin k),
          @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
              (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active e →
            @LE.le.{0} Real Real.instLE
              (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (p (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e))
                (p (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e)))
              (w e)) →
        @LE.le.{0} Real Real.instLE (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) (p u) (p v))
          (@List.sum.{0} Real Real.instAdd Real.instZero (@List.map.{0, 0} (Fin k) Real w es))) ∧ ((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Real),
  (∀ (e : Fin k),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (w e)) →
    ∀ (B : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) B →
        ∀ (u v : Fin n) (p : Fin n → Real),
          (∀ (e : Fin k),
              @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
                  (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active
                  e →
                @LE.le.{0} Real Real.instLE
                  (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                    (p (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e))
                    (p (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e)))
                  (w e)) →
            @LT.lt.{0} Real Real.instLT (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B u v) B →
              @LE.le.{0} Real Real.instLE (p u)
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (p v)
                  (@DecrAlmostLinearSSSP.Decremental.cappedDistance n k g active w B u v))) ∧ (∀ {k : Nat} (w : Fin k → Nat) (es : List.{0} (Fin k)),
  @Eq.{1} Real
    (@Nat.cast.{0} Real Real.instNatCast
      (@List.sum.{0} Nat instAddNat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)
        (@List.map.{0, 0} (Fin k) Nat w es)))
    (@List.sum.{0} Real Real.instAdd Real.instZero
      (@List.map.{0, 0} (Fin k) Real (fun e => @Nat.cast.{0} Real Real.instNatCast (w e)) es))))))) ∧ ((((∀ {k : Nat} (w : Fin k → Nat) (W : Nat),
  (∀ (e : Fin k), @LE.le.{0} Nat instLENat (w e) W) →
    ∀ (es : List.{0} (Fin k)),
      @LE.le.{0} Nat instLENat
        (@List.sum.{0} Nat instAddNat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass)
          (@List.map.{0, 0} (Fin k) Nat w es))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) (@List.length.{0} (Fin k) es) W)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (active : Finset.{0} (Fin i.k)) (v : Fin i.n),
      @DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph active i.source v →
        ∃ d,
          And
            (@LE.le.{0} Nat instLENat d
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) i.n
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                i.W))
            (@Eq.{1} ENNReal
              (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
                (fun e =>
                  @Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (i.weight e))
                i.source v)
              (@Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                d)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input),
  i.Valid →
    ∀ (active : Finset.{0} (Fin i.k)) (u : Fin i.n) (d : Nat),
      @Eq.{1} ENNReal
          (@DecrAlmostLinearSSSP.Decremental.distance i.n i.k i.graph active
            (fun e =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                (i.weight e))
            i.source u)
          (@Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            d) →
        @DecrAlmostLinearSSSP.Decremental.Reachable i.n i.k i.graph active i.source u →
          ∀ (e : Fin i.k),
            @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d (i.weight e))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) i.n i.W)) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Nat)
  (s : Fin n) (z : Fin n → Nat),
  @Eq.{1} Nat (z s) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    (∀ (e : Fin k),
        @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
            (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active e →
          @LE.le.{0} Nat instLENat (z (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (z (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e)) (w e))) →
      ∀ (v : Fin n),
        @LE.le.{0} ENNReal ENNReal.instLE
          (@Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (z v))
          (@DecrAlmostLinearSSSP.Decremental.distance n k g active
            (fun e =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                (w e))
            s v)))) ∧ (((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source : Fin n} {tentative : Fin n → Option.{0} Nat} {settled : Finset.{0} (Fin n)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))},
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled queue →
    ∀ (key : Nat) (v : Fin n),
      @Membership.mem.{0, 0} (Prod.{0, 0} Nat (Fin n)) (Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
          (@Multiset.instMembership.{0} (Prod.{0, 0} Nat (Fin n))) queue (@Prod.mk.{0, 0} Nat (Fin n) key v) →
        (∀ (item : Prod.{0, 0} Nat (Fin n)),
            @Membership.mem.{0, 0} (Prod.{0, 0} Nat (Fin n)) (Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
                (@Multiset.instMembership.{0} (Prod.{0, 0} Nat (Fin n))) queue item →
              @LE.le.{0} Nat instLENat key (@Prod.fst.{0, 0} Nat (Fin n) item)) →
          v ∉ settled →
            And (@Eq.{1} (Option.{0} Nat) (tentative v) (@Option.some.{0} Nat key))
              (@Eq.{1} ENNReal
                (@DecrAlmostLinearSSSP.Decremental.distance n k g active
                  (fun e =>
                    @Nat.cast.{0} ENNReal
                      (@AddMonoidWithOne.toNatCast.{0} ENNReal
                        (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                      (w e))
                  source v)
                (@Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  key))) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → ENNReal)
  (s : Fin n),
  @Eq.{1} ENNReal (@DecrAlmostLinearSSSP.Decremental.distance n k g active w s s)
    (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero)))) ∧ ((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → ENNReal)
  (s v : Fin n) (d : Nat),
  @LE.le.{0} ENNReal ENNReal.instLE (@DecrAlmostLinearSSSP.Decremental.distance n k g active w s v)
      (@Nat.cast.{0} ENNReal
        (@AddMonoidWithOne.toNatCast.{0} ENNReal
          (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
        d) →
    @DecrAlmostLinearSSSP.Decremental.Reachable n k g active s v) ∧ ((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Nat)
  (s : Fin n) (e : Fin k),
  @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
      (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active e →
    ∀ (d : Nat),
      @LE.le.{0} ENNReal ENNReal.instLE
          (@DecrAlmostLinearSSSP.Decremental.distance n k g active
            (fun a =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                (w a))
            s (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e))
          (@Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            d) →
        @LE.le.{0} ENNReal ENNReal.instLE
          (@DecrAlmostLinearSSSP.Decremental.distance n k g active
            (fun a =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                (w a))
            s (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e))
          (@Nat.cast.{0} ENNReal
            (@AddMonoidWithOne.toNatCast.{0} ENNReal
              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) d (w e)))) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (active : Finset.{0} (Fin k)) (w : Fin k → Nat)
  (source : Fin n),
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source
    (@DecrAlmostLinearSSSP.Decremental.Exact.initialTentative n source)
    (@EmptyCollection.emptyCollection.{0} (Finset.{0} (Fin n)) (@Finset.instEmptyCollection.{0} (Fin n)))
    (@Singleton.singleton.{0, 0} (Prod.{0, 0} Nat (Fin n)) (Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
      (@Multiset.instSingleton.{0} (Prod.{0, 0} Nat (Fin n)))
      (@Prod.mk.{0, 0} Nat (Fin n) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) source)))))))) ∧ (((((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {u v : Fin n}
  {es : List.{0} (Fin k)},
  @DecrAlmostLinearSSSP.Decremental.Walk n k g active u v es →
    ∀ (P : Fin n → Prop),
      (∀ (e : Fin k),
          @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
              (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k))) active e →
            P (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) →
              P (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e)) →
        P u → P v) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source : Fin n} {tentative : Fin n → Option.{0} Nat} {settled : Finset.{0} (Fin n)},
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled
      (@OfNat.ofNat.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) (nat_lit 0)
        (@Zero.toOfNat0.{0} (Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
          (@Multiset.instZero.{0} (Prod.{0, 0} Nat (Fin n))))) →
    ∀ (v : Fin n),
      And
        (@Eq.{1} ENNReal
          (@DecrAlmostLinearSSSP.Decremental.distance n k g active
            (fun e =>
              @Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                (w e))
            source v)
          (DecrAlmostLinearSSSP.Decremental.Exact.tentativeValue (tentative v)))
        (Iff (@Eq.{1} (Option.{0} Nat) (tentative v) (@Option.none.{0} Nat))
          (Not (@DecrAlmostLinearSSSP.Decremental.Reachable n k g active source v))))) ∧ ((∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source : Fin n} {tentative : Fin n → Option.{0} Nat} {settled : Finset.{0} (Fin n)}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))},
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled queue →
    ∀ (target : Fin n) (candidate : Nat),
      target ∉ settled →
        (∀ (d : Nat),
            @Eq.{1} (Option.{0} Nat) (tentative target) (@Option.some.{0} Nat d) →
              @LT.lt.{0} Nat instLTNat candidate d) →
          @LE.le.{0} ENNReal ENNReal.instLE
              (@DecrAlmostLinearSSSP.Decremental.distance n k g active
                (fun e =>
                  @Nat.cast.{0} ENNReal
                    (@AddMonoidWithOne.toNatCast.{0} ENNReal
                      (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                    (w e))
                source target)
              (@Nat.cast.{0} ENNReal
                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                candidate) →
            (∀ (v : Fin n),
                @Membership.mem.{0, 0} (Fin n) (Finset.{0} (Fin n))
                    (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin n)) (Fin n) (@Finset.instSetLike.{0} (Fin n)))
                    settled v →
                  ∀ (d : Nat),
                    @Eq.{1} (Option.{0} Nat) (tentative v) (@Option.some.{0} Nat d) →
                      @LE.le.{0} Nat instLENat d candidate) →
              @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source
                (@Function.update.{1, 1} (Fin n) (fun a => Option.{0} Nat) (instDecidableEqFin n) tentative target
                  (@Option.some.{0} Nat candidate))
                settled
                (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) candidate target) queue)) ∧ (∀ {n k : Nat} {g : DecrAlmostLinearSSSP.Decremental.Digraph n k} {active : Finset.{0} (Fin k)} {w : Fin k → Nat}
  {source : Fin n} {tentative : Fin n → Option.{0} Nat} {settled : Finset.{0} (Fin n)}
  {remaining : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} (key : Nat) (v : Fin n),
  @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative settled
      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) remaining) →
    v ∉ settled →
      @Eq.{1} (Option.{0} Nat) (tentative v) (@Option.some.{0} Nat key) →
        @Eq.{1} ENNReal
            (@DecrAlmostLinearSSSP.Decremental.distance n k g active
              (fun e =>
                @Nat.cast.{0} ENNReal
                  (@AddMonoidWithOne.toNatCast.{0} ENNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                  (w e))
              source v)
            (@Nat.cast.{0} ENNReal
              (@AddMonoidWithOne.toNatCast.{0} ENNReal
                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
              key) →
          (∀ (item : Prod.{0, 0} Nat (Fin n)),
              @Membership.mem.{0, 0} (Prod.{0, 0} Nat (Fin n)) (Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
                  (@Multiset.instMembership.{0} (Prod.{0, 0} Nat (Fin n))) remaining item →
                @LE.le.{0} Nat instLENat key (@Prod.fst.{0, 0} Nat (Fin n) item)) →
            (∀ (e : Fin k),
                @Membership.mem.{0, 0} (Fin k) (Finset.{0} (Fin k))
                    (@SetLike.instMembership.{0, 0} (Finset.{0} (Fin k)) (Fin k) (@Finset.instSetLike.{0} (Fin k)))
                    active e →
                  @Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) v →
                    ∃ dh,
                      And
                        (@Eq.{1} (Option.{0} Nat) (tentative (@DecrAlmostLinearSSSP.Decremental.Digraph.head n k g e))
                          (@Option.some.{0} Nat dh))
                        (@LE.le.{0} Nat instLENat dh
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) key (w e)))) →
              @DecrAlmostLinearSSSP.Decremental.Exact.LabelInvariant n k g active w source tentative
                (@Insert.insert.{0, 0} (Fin n) (Finset.{0} (Fin n))
                  (@Finset.instInsert.{0} (Fin n) (instDecidableEqFin n)) v settled)
                remaining))) ∧ (((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (t : Nat) (ht : @LT.lt.{0} Nat instLTNat t k)
  (v : Fin n),
  @Eq.{1} (List.{0} (Fin k))
    (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
      v)
    (@ite.{1} (List.{0} (Fin k))
      (@Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g (@Fin.mk k t ht)) v)
      (instDecidableEqFin n (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g (@Fin.mk k t ht)) v)
      (@List.cons.{0} (Fin k) (@Fin.mk k t ht) (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g t v))
      (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g t v))) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (t : Nat) (v : Fin n) (e : Fin k),
  Iff
    (@Membership.mem.{0, 0} (Fin k) (List.{0} (Fin k)) (@List.instMembership.{0} (Fin k))
      (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g t v) e)
    (And (@LT.lt.{0} Nat instLTNat (@Fin.val k e) t)
      (@Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) v)))) ∧ ((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (t : Nat) (v : Fin n),
  @List.Nodup.{0} (Fin k) (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g t v)) ∧ ((∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (t : Nat),
  @LE.le.{0} Nat instLENat t k →
    @Eq.{1} Nat (∑ v, @List.length.{0} (Fin k) (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g t v)) t) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.clearPrepare s
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.clearPrepared s)))))) ∧ ((((∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.prepare s
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
    (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.prepared s)) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.edge s
    (@OfNat.ofNat.{0} Nat (nat_lit 20) (instOfNatNat (nat_lit 20)))
    (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.advanced s))) ∧ ((∀
  j ∉
    @Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 294) (instOfNatNat (nat_lit 294)))
      (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 296) (instOfNatNat (nat_lit 296)))
        (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 298) (instOfNatNat (nat_lit 298)))
          (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 300) (instOfNatNat (nat_lit 300)))
            (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 304) (instOfNatNat (nat_lit 304)))
              (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 306) (instOfNatNat (nat_lit 306)))
                (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308)))
                  (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310)))
                    (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 312) (instOfNatNat (nat_lit 312)))
                      (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 314) (instOfNatNat (nat_lit 314)))))))))))),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.edge j) ∧ ((∀ (j : Nat),
  DecrAlmostLinearSSSP.Decremental.Structured.RealFrame DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code j) ∧ (∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
    have tail := s.natMem (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 298) (instOfNatNat (nat_lit 298))));
    have head :=
      s.natMem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 298) (instOfNatNat (nat_lit 298))))
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))));
    have weight :=
      s.natMem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 298) (instOfNatNat (nat_lit 298))))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))));
    have headSlot :=
      @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 224) (instOfNatNat (nat_lit 224)))) tail;
    have next := s.natMem headSlot;
    have node := s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 296) (instOfNatNat (nat_lit 296)));
    And
      (@Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.advanced s).natMem
        (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
          (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
            (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
              (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat
                  (@Function.update.{1, 1} Nat (fun a => Nat) instDecidableEqNat s.natMem node head)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) node
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 294) (instOfNatNat (nat_lit 294)))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) node
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                next)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) node
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              weight)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 294) (instOfNatNat (nat_lit 294))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          headSlot node))
      (And
        (@Eq.{1} Nat
          ((DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.advanced s).natReg
            (@OfNat.ofNat.{0} Nat (nat_lit 294) (instOfNatNat (nat_lit 294))))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 294) (instOfNatNat (nat_lit 294))))
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.advanced s).natReg
              (@OfNat.ofNat.{0} Nat (nat_lit 296) (instOfNatNat (nat_lit 296))))
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 296) (instOfNatNat (nat_lit 296))))
              (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
          (And
            (@Eq.{1} Nat
              ((DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.advanced s).natReg
                (@OfNat.ofNat.{0} Nat (nat_lit 298) (instOfNatNat (nat_lit 298))))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 298) (instOfNatNat (nat_lit 298))))
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (And
              (@Eq.{1} Nat
                ((DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.advanced s).natReg
                  (@OfNat.ofNat.{0} Nat (nat_lit 300) (instOfNatNat (nat_lit 300))))
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 300) (instOfNatNat (nat_lit 300))))
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
              (@Eq.{1} (Nat → Real) (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.advanced s).realMem
                s.realMem))))))))) ∧ (((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input) (e : Fin i.k)
  (offset : Nat),
  @LT.lt.{0} Nat instLTNat offset (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @Eq.{1} Nat
      ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) (@Fin.val i.k e)))
          offset))
      (@ite.{1} Nat (@Eq.{1} Nat offset (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (instDecidableEqNat offset (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.tail i.n i.k i.graph e))
        (@ite.{1} Nat (@Eq.{1} Nat offset (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (instDecidableEqNat offset (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e)) (i.weight e)))) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input) (address : Nat),
  @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
      address →
    @Eq.{1} Nat ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem address)
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input) (address : Nat),
  @Eq.{1} Real ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).realMem address)
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) ∧ ((∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input) (B F : Nat),
  @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
      B →
    @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) F →
      ∀ (address : Nat),
        And
          (@Eq.{1} Nat
            ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).natMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) address)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@Eq.{1} Real
            ((DecrAlmostLinearSSSP.Decremental.initialMachine p i).realMem
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) B
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) F
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) address)
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))) ∧ (∀ (p : DecrAlmostLinearSSSP.Decremental.Program) (i : DecrAlmostLinearSSSP.Decremental.Input),
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape i
    (DecrAlmostLinearSSSP.Decremental.Structured.data (DecrAlmostLinearSSSP.Decremental.initialMachine p i))))))))) ∧ ((((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s t : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape i s →
    (∀ (a : Nat),
        @LT.lt.{0} Nat instLTNat a
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k)) →
          @Eq.{1} Nat (t.natMem a) (s.natMem a)) →
      DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape i t) ∧ (∀ (l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses) {k : Nat} (e : Fin k) (es : List.{0} (Fin k)),
  @Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.root l k (@List.cons.{0} (Fin k) e es))
    (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress l k e))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (e : Fin i.k),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
    (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress
      (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        i.n i.k)
      i.k e)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (e : Fin i.k) (memory : Nat → Nat) (v : Fin i.n),
  have l :=
    DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      i.n i.k;
  @Eq.{1} Nat
    (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.insertMemory i l e memory
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.heads (@Fin.val i.n v)))
    (@ite.{1} Nat (@Eq.{1} (Fin i.n) v (@DecrAlmostLinearSSSP.Decremental.Digraph.tail i.n i.k i.graph e))
      (instDecidableEqFin i.n v (@DecrAlmostLinearSSSP.Decremental.Digraph.tail i.n i.k i.graph e))
      (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress l i.k e)
      (memory (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.heads (@Fin.val i.n v))))))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (e f : Fin i.k) (memory : Nat → Nat),
  have l :=
    DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      i.n i.k;
  @Eq.{1} Nat
    (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.insertMemory i l e memory
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.active (@Fin.val i.k f)))
    (@ite.{1} Nat (@Eq.{1} (Fin i.k) f e) (instDecidableEqFin i.k f e)
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
      (memory (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.active (@Fin.val i.k f))))) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (e f : Fin i.k),
  @Ne.{1} (Fin i.k) f e →
    ∀ (r : Nat),
      @LT.lt.{0} Nat instLTNat r (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
        ∀ (memory : Nat → Nat),
          have l :=
            DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              i.n i.k;
          @Eq.{1} Nat
            (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.insertMemory i l e memory
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress l i.k f) r))
            (memory
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress l i.k f) r)))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (e : Fin i.k) (memory : Nat → Nat),
  have l :=
    DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      i.n i.k;
  have updated := DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.insertMemory i l e memory;
  And
    (@Eq.{1} Nat (updated (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress l i.k e))
      (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.head i.n i.k i.graph e)))
    (And
      (@Eq.{1} Nat
        (updated
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress l i.k e)
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.active (@Fin.val i.k e)))
      (And
        (@Eq.{1} Nat
          (updated
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress l i.k e)
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (memory
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.heads
              (@Fin.val i.n (@DecrAlmostLinearSSSP.Decremental.Digraph.tail i.n i.k i.graph e)))))
        (@Eq.{1} Nat
          (updated
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress l i.k e)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (i.weight e))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (e : Fin i.k) (memory : Nat → Nat) (a : Nat),
  Or
      (@LT.lt.{0} Nat instLTNat a
        (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            i.n i.k).heads)
      (@LE.le.{0} Nat instLENat
        (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            i.n i.k).powers
        a) →
    @Eq.{1} Nat
      (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.insertMemory i
        (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          i.n i.k)
        e memory a)
      (memory a)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (t : Nat) (ht : @LT.lt.{0} Nat instLTNat t i.k)
  (s u : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Image i
      (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        i.n i.k)
      t s →
    @Eq.{1} (Nat → Nat) u.natMem
        (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.insertMemory i
          (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            i.n i.k)
          (@Fin.mk i.k t ht) s.natMem) →
      DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Image i
        (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          i.n i.k)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) t
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        u))))) ∧ ((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (upto : Nat) (ht : @LT.lt.{0} Nat instLTNat upto i.k)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.Prefix i upto s →
    @Eq.{1} (Nat → Nat) (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.advanced s).natMem
      (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.insertMemory i
        (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          i.n i.k)
        (@Fin.mk i.k upto ht) s.natMem)) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (upto : Nat),
  @LT.lt.{0} Nat instLTNat upto i.k →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.Prefix i upto s →
        DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.Prefix i
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto
            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.advanced s))) ∧ ((∀
  j ∉
    @Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 294) (instOfNatNat (nat_lit 294)))
      (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 296) (instOfNatNat (nat_lit 296)))
        (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 298) (instOfNatNat (nat_lit 298)))
          (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 300) (instOfNatNat (nat_lit 300)))
            (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 304) (instOfNatNat (nat_lit 304)))
              (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 306) (instOfNatNat (nat_lit 306)))
                (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308)))
                  (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310)))
                    (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 312) (instOfNatNat (nat_lit 312)))
                      (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 314) (instOfNatNat (nat_lit 314)))))))))))),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.loop j) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (remaining upto : Nat),
  @Eq.{1} Nat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) upto remaining) i.k →
    ∀ (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
      DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.Prefix i upto s →
        ∃ t,
          And
            (DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.loop
              s
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) remaining)
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              t)
            (And (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.Prefix i i.k t)
              (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                (∀ (a : Nat),
                  Or
                      (@LT.lt.{0} Nat instLTNat a
                        (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            i.n i.k).heads)
                      (@LE.le.{0} Nat instLENat
                        (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
                            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            i.n i.k).powers
                        a) →
                    @Eq.{1} Nat (t.natMem a) (s.natMem a))))) ∧ (∀
  j ∉
    @Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 290) (instOfNatNat (nat_lit 290)))
      (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 292) (instOfNatNat (nat_lit 292)))
        (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 294) (instOfNatNat (nat_lit 294)))
          (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 296) (instOfNatNat (nat_lit 296)))
            (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 298) (instOfNatNat (nat_lit 298)))
              (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                (@OfNat.ofNat.{0} Nat (nat_lit 300) (instOfNatNat (nat_lit 300)))))))),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.setup j)))) ∧ (((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) i.n →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))) i.k →
          DecrAlmostLinearSSSP.Decremental.Exact.Layout.Image
              (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                i.n i.k)
              s →
            DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape i s →
              ∃ t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.setup s
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i.n)
                      (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))
                    t)
                  (And
                    (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.Prefix i
                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) t)
                    (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                      (∀ (a : Nat),
                        Or
                            (@LT.lt.{0} Nat instLTNat a
                              (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  i.n i.k).heads)
                            (@LE.le.{0} Nat instLENat
                              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    i.n i.k).heads
                                i.n)
                              a) →
                          @Eq.{1} Nat (t.natMem a) (s.natMem a))))) ∧ (∀ {s u t : DecrAlmostLinearSSSP.Decremental.Structured.Data} {c d : Nat},
  DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.setup s c u →
    DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.loop u d t →
      DecrAlmostLinearSSSP.Decremental.Structured.Eval DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code s
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) c d) t)) ∧ ((∀
  j ∉
    @Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 290) (instOfNatNat (nat_lit 290)))
      (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 292) (instOfNatNat (nat_lit 292)))
        (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 294) (instOfNatNat (nat_lit 294)))
          (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 296) (instOfNatNat (nat_lit 296)))
            (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 298) (instOfNatNat (nat_lit 298)))
              (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 300) (instOfNatNat (nat_lit 300)))
                (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                  (@OfNat.ofNat.{0} Nat (nat_lit 304) (instOfNatNat (nat_lit 304)))
                  (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                    (@OfNat.ofNat.{0} Nat (nat_lit 306) (instOfNatNat (nat_lit 306)))
                    (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 308) (instOfNatNat (nat_lit 308)))
                      (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                        (@OfNat.ofNat.{0} Nat (nat_lit 310) (instOfNatNat (nat_lit 310)))
                        (@Insert.insert.{0, 0} Nat (Finset.{0} Nat) (@Finset.instInsert.{0} Nat instDecidableEqNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 312) (instOfNatNat (nat_lit 312)))
                          (@Singleton.singleton.{0, 0} Nat (Finset.{0} Nat) (@Finset.instSingleton.{0} Nat)
                            (@OfNat.ofNat.{0} Nat (nat_lit 314) (instOfNatNat (nat_lit 314)))))))))))))),
  DecrAlmostLinearSSSP.Decremental.Structured.NatFrame DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code j) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (s : DecrAlmostLinearSSSP.Decremental.Structured.Data),
  @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 56) (instOfNatNat (nat_lit 56))))
      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
    @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 26) (instOfNatNat (nat_lit 26))))
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 66) (instOfNatNat (nat_lit 66)))) i.n →
        @Eq.{1} Nat (s.natReg (@OfNat.ofNat.{0} Nat (nat_lit 68) (instOfNatNat (nat_lit 68)))) i.k →
          DecrAlmostLinearSSSP.Decremental.Exact.Layout.Image
              (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                i.n i.k)
              s →
            DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Tape i s →
              ∃ t,
                And
                  (DecrAlmostLinearSSSP.Decremental.Structured.Eval
                    DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.code s
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) i.n)
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (@OfNat.ofNat.{0} Nat (nat_lit 22) (instOfNatNat (nat_lit 22))) i.k))
                      (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
                    t)
                  (And (DecrAlmostLinearSSSP.Decremental.Exact.AdjacencyBuild.Prefix i i.k t)
                    (And (@Eq.{1} (Nat → Real) t.realMem s.realMem)
                      (∀ (a : Nat),
                        Or
                            (@LT.lt.{0} Nat instLTNat a
                              (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  i.n i.k).heads)
                            (@LE.le.{0} Nat instLENat
                              (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
                                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
                                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  i.n i.k).powers
                              a) →
                          @Eq.{1} Nat (t.natMem a) (s.natMem a))))) ∧ (∀ {n k : Nat} (g : DecrAlmostLinearSSSP.Decremental.Digraph n k) (upto : Nat) (v : Fin n) (e : Fin k)
  (es : List.{0} (Fin k)),
  @Eq.{1} (List.{0} (Fin k)) (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g upto v)
      (@List.cons.{0} (Fin k) e es) →
    And (@Eq.{1} (List.{0} (Fin k)) es (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency n k g (@Fin.val k e) v))
      (And (@Eq.{1} (Fin n) (@DecrAlmostLinearSSSP.Decremental.Digraph.tail n k g e) v)
        (@LT.lt.{0} Nat instLTNat (@Fin.val k e) upto)))))))) ∧ (((((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses)
  (s : DecrAlmostLinearSSSP.Decremental.Structured.Data) (upto : Nat),
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Image i l upto s →
    ∀ (v : Fin i.n),
      @DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Chain i.k l s
        (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency i.n i.k i.graph upto v)) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Image i l i.k s →
    DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i l s)) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Image i l i.k s →
    DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.ActiveImage i l (@List.nil.{0} (Fin i.k)) s) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i l s →
    (∀ (a : Nat),
        @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
            (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
            (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.staticFootprint i l) a →
          @Eq.{1} Nat (t.natMem a) (s.natMem a)) →
      DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i l t))) ∧ (((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.StaticImage i l s →
    ∀ (v : Fin i.n),
      @DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.Chain i.k l s
        (@DecrAlmostLinearSSSP.Decremental.Exact.adjacency i.n i.k i.graph i.k v)) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {tentative : Fin i.n → Option.{0} Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative s →
    ∀ (v : Fin i.n) (d : Nat),
      @Eq.{1} (Option.{0} Nat) (tentative v) (@Option.some.{0} Nat d) →
        And (@Eq.{1} Nat (s.natMem (@Fin.val i.n v)) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (And
            (@Eq.{1} Nat
              (s.natMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.distances (@Fin.val i.n v)))
              d)
            (@Eq.{1} Real (s.realMem (@Fin.val i.n v)) (@Nat.cast.{0} Real Real.instNatCast d))))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {tentative : Fin i.n → Option.{0} Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative s →
    ∀ (v : Fin i.n),
      @Eq.{1} (Option.{0} Nat) (tentative v) (@Option.none.{0} Nat) →
        @Eq.{1} Nat (s.natMem (@Fin.val i.n v)) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) ∧ ((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {tentative : Fin i.n → Option.{0} Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative s →
    ∀ (v : Fin i.n),
      Iff (@Eq.{1} Nat (s.natMem (@Fin.val i.n v)) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
        (@Eq.{1} (Option.{0} Nat) (tentative v) (@Option.none.{0} Nat))) ∧ (∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {tentative : Fin i.n → Option.{0} Nat} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative s →
    ∀ (v : Fin i.n),
      @Eq.{1} ENNReal (DecrAlmostLinearSSSP.Decremental.stored s.machine (@Fin.val i.n v))
        (DecrAlmostLinearSSSP.Decremental.Exact.tentativeValue (tentative v))))))) ∧ ((((∀ {i : DecrAlmostLinearSSSP.Decremental.Input} {l : DecrAlmostLinearSSSP.Decremental.Exact.Layout.Addresses}
  {tentative : Fin i.n → Option.{0} Nat} {s t : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative s →
    (∀ (v : Fin i.n), @Eq.{1} Nat (t.natMem (@Fin.val i.n v)) (s.natMem (@Fin.val i.n v))) →
      (∀ (v : Fin i.n),
          @Eq.{1} Nat
            (t.natMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.distances (@Fin.val i.n v)))
            (s.natMem (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.distances (@Fin.val i.n v)))) →
        (∀ (v : Fin i.n), @Eq.{1} Real (t.realMem (@Fin.val i.n v)) (s.realMem (@Fin.val i.n v))) →
          DecrAlmostLinearSSSP.Decremental.Exact.TentativeImage i l tentative t) ∧ (∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (v : Fin i.n),
  have l :=
    DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      i.n i.k;
  And (@LT.lt.{0} Nat instLTNat (@Fin.val i.n v) l.heads)
    (And
      (@LT.lt.{0} Nat instLTNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.heads (@Fin.val i.n v)) l.powers)
      (And
        (@LT.lt.{0} Nat instLTNat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.settled (@Fin.val i.n v)) l.powers)
        (@LT.lt.{0} Nat instLTNat
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.distances (@Fin.val i.n v)) l.powers))))) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (e : Fin i.k) (r : Nat),
  @LT.lt.{0} Nat instLTNat r (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) →
    have l :=
      DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        i.n i.k;
    And
      (@LT.lt.{0} Nat instLTNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) l.active (@Fin.val i.k e)) l.powers)
      (@LT.lt.{0} Nat instLTNat
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
          (@DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.nodeAddress l i.k e) r)
        l.powers)) ∧ ((∀ (i : DecrAlmostLinearSSSP.Decremental.Input) (a : Nat),
  @Membership.mem.{0, 0} Nat (Finset.{0} Nat)
      (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat))
      (DecrAlmostLinearSSSP.Decremental.Exact.Adjacency.staticFootprint i
        (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          i.n i.k))
      a →
    @LT.lt.{0} Nat instLTNat a
      (DecrAlmostLinearSSSP.Decremental.Exact.Layout.addresses
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) i.n
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) i.k))
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          i.n i.k).powers) ∧ (∀ {n : Nat} (q : Multiset.{0} (Prod.{0, 0} Nat (Fin n))),
  @Eq.{1} Nat (@Multiset.card.{0} (Prod.{0, 0} Nat Nat) (@DecrAlmostLinearSSSP.Decremental.Exact.queueMap n q))
    (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) q))))) ∧ (((∀ {n : Nat} (key : Nat) (v : Fin n) (q : Multiset.{0} (Prod.{0, 0} Nat (Fin n))),
  @Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat))
    (@DecrAlmostLinearSSSP.Decremental.Exact.queueMap n
      (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) q))
    (@Multiset.cons.{0} (Prod.{0, 0} Nat Nat) (@Prod.mk.{0, 0} Nat Nat key (@Fin.val n v))
      (@DecrAlmostLinearSSSP.Decremental.Exact.queueMap n q))) ∧ (∀ {n h : Nat} (tree : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h) (q : Multiset.{0} (Prod.{0, 0} Nat (Fin n))),
  @Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (@DecrAlmostLinearSSSP.Decremental.Exact.queueMap n q)
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries h tree
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
    @Eq.{1} Nat (@DecrAlmostLinearSSSP.Decremental.RadixQueue.count h tree)
      (@Multiset.card.{0} (Prod.{0, 0} Nat (Fin n)) q))) ∧ ((∀ {n h : Nat} (tree next : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h)
  (q : Multiset.{0} (Prod.{0, 0} Nat (Fin n))) (key value : Nat),
  @Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (@DecrAlmostLinearSSSP.Decremental.Exact.queueMap n q)
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries h tree
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
    @Eq.{1} (Option.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h))))
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.pop h tree)
        (@Option.some.{0} (Prod.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h)))
          (@Prod.mk.{0, 0} Nat (Prod.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h)) key
            (@Prod.mk.{0, 0} Nat (DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h) value next))) →
      ∃ v remaining,
        And (@Eq.{1} Nat (@Fin.val n v) value)
          (And
            (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat (Fin n))) q
              (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) remaining))
            (And
              (@Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat))
                (@DecrAlmostLinearSSSP.Decremental.Exact.queueMap n remaining)
                (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries h next
                  (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))
              (∀ (item : Prod.{0, 0} Nat (Fin n)),
                @Membership.mem.{0, 0} (Prod.{0, 0} Nat (Fin n)) (Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
                    (@Multiset.instMembership.{0} (Prod.{0, 0} Nat (Fin n))) q item →
                  @LE.le.{0} Nat instLENat key (@Prod.fst.{0, 0} Nat (Fin n) item))))) ∧ ((∀ {n h : Nat} (tree : DecrAlmostLinearSSSP.Decremental.RadixQueue.Trie h) (q : Multiset.{0} (Prod.{0, 0} Nat (Fin n)))
  (key : Nat) (v : Fin n),
  @Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat)) (@DecrAlmostLinearSSSP.Decremental.Exact.queueMap n q)
      (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries h tree
        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))) →
    @LT.lt.{0} Nat instLTNat key
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h) →
      @Eq.{1} (Multiset.{0} (Prod.{0, 0} Nat Nat))
        (@DecrAlmostLinearSSSP.Decremental.Exact.queueMap n
          (@Multiset.cons.{0} (Prod.{0, 0} Nat (Fin n)) (@Prod.mk.{0, 0} Nat (Fin n) key v) q))
        (@DecrAlmostLinearSSSP.Decremental.RadixQueue.entries h
          (DecrAlmostLinearSSSP.Decremental.RadixQueue.insert h key (@Fin.val n v) tree)
          (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))) ∧ (∀ {n h base slot : Nat} {tree : DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie h}
  {queue : Multiset.{0} (Prod.{0, 0} Nat (Fin n))} {s : DecrAlmostLinearSSSP.Decremental.Structured.Data},
  @DecrAlmostLinearSSSP.Decremental.Exact.Heap.Image n h base slot tree queue s →
    slot ∉ @DecrAlmostLinearSSSP.Decremental.Exact.LocatedTrie.footprint h tree)))))))) := by sorry
