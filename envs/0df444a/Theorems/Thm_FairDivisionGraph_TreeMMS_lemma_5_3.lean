-- Prove2me | Theorems.Thm_FairDivisionGraph_TreeMMS_lemma_5_3
-- name    : FairDivisionGraph.TreeMMS.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:21:19.547918+00:00
-- url     : https://prove2.me/theorems/0ed30ed9-c2ab-4935-b5d9-2c1025129718
-- title:
--   Lemma 5.3 — exact polynomial-time computation of connected MMS
-- statement:
--   There is one polynomial-time bit-string function which, given any normalized nonnegative rational CFD instance on a finite tree with $1\le n\le m$ and a selected agent $i$, returns a rational number equal to
--   $$\max_{P\text{ a connected }n\text{-partition of }V}\min_{j<n}u_i(P_j).$$
--   The input includes the graph, the entire rational utility table, and the selected agent index. The output is decoded as an exact rational number, with no approximation tolerance. One finite-alphabet machine and one polynomial time bound apply uniformly to every dimension, agent and bit length. Its polynomial-time termination also covers malformed bit strings, on which no correctness is required.
--
--   The statement computes the benchmark itself, rather than merely asserting its attainment or supplying it as an input.
--
--   Differences from the source:
--   - encoding: finite vertex and player sets, with players numbered 1 through n → vertices Fin m and agents Fin n, both zero-based; reason: finite relabelling changes no instance
--   - encoding: valid allocations and connected partitions → valid bundles may be empty; partition parts are nonempty; MMS is a finite maximum totalized by zero outside its meaningful domain; reason: the empty allocation is expressly permitted and tree partitions exist throughout the theorem domain
--   - encoding: polynomial-time computation with rational utilities → one finite-alphabet TM2-computable bit-string function with one polynomial bound, on binary graph and rational utility codes; reason: makes uniform bit complexity explicit; malformed words must terminate but have no correctness promise
--   - encoding: a player i in the input instance → the zero-based player index is appended in self-delimiting binary; reason: makes the selection explicit in the uniform input
--   - encoding: utilities are rational for computational purposes → rational entries with exact signed-numerator and positive-denominator decoding; reason: uses the computational domain stated in §2, without changing the real-valued existence theorem
-- source:
--   Bouveret, Cechlárová, Elkind, Igarashi and Peters (2017), Fair Division of a Graph, IJCAI-17, https://doi.org/10.24963/ijcai.2017/20, Lemma 5.3, printed p. 140 (PDF p. 6)

import Definitions.Def_FairDivisionGraph_TreeMMS_Encoding

set_option autoImplicit false

namespace FairDivisionGraph.TreeMMS

/-- Lemma 5.3: one polynomial-time bit algorithm computes every selected exact rational MMS. -/
theorem lemma_5_3 :
    ∃ f : List Bool → List Bool, Grunbaum2003.ContainmentPolyTime f ∧ ComputesMMS f := by sorry

end FairDivisionGraph.TreeMMS

/-
BEGIN IMPORTED DEPENDENCY SOURCE

MODULE: Model
SHA256: 296ea53e433168aed88ae50d3345cd5d66705c6f11d264712fdc401f7adc3ca0

import Mathlib

set_option autoImplicit false

namespace FairDivisionGraph.TreeMMS

/-- Additive value; no normalization is built into this raw operation. -/
def value {m : ℕ} (u : Fin m → ℝ) (S : Finset (Fin m)) : ℝ := ∑ v ∈ S, u v

/-- Initial CFD utility assumptions, including the standing cardinality convention. -/
def IsCFD {m n : ℕ} (u : Fin n → Fin m → ℝ) : Prop :=
  0 < n ∧ n ≤ m ∧ (∀ i v, 0 ≤ u i v) ∧ (∀ i, value (u i) Finset.univ = 1)

/-- Empty bundles are permitted; every nonempty bundle induces a connected graph. -/
def BundleConnected {m : ℕ} (G : SimpleGraph (Fin m)) (S : Finset (Fin m)) : Prop :=
  S = ∅ ∨ (G.induce (S : Set (Fin m))).Connected

/-- General valid allocations need not cover all vertices. -/
def Valid {m n : ℕ} (G : SimpleGraph (Fin m)) (π : Fin n → Finset (Fin m)) : Prop :=
  (∀ i, BundleConnected G (π i)) ∧ (∀ i j, i ≠ j → Disjoint (π i) (π j))

/-- Completeness is separate from validity. -/
def Complete {m n : ℕ} (π : Fin n → Finset (Fin m)) : Prop :=
  ∀ v, ∃ i, v ∈ π i

/-- A labelled partition of a residual vertex set into nonempty connected parts. -/
def ConnectedPartition {m k : ℕ} (G : SimpleGraph (Fin m))
    (V : Finset (Fin m)) (P : Fin k → Finset (Fin m)) : Prop :=
  (∀ j, P j ⊆ V ∧ (P j).Nonempty ∧ (G.induce (P j : Set (Fin m))).Connected) ∧
  (∀ j l, j ≠ l → Disjoint (P j) (P l)) ∧
  (∀ v, v ∈ V ↔ ∃ j, v ∈ P j)

end FairDivisionGraph.TreeMMS

MODULE: MMS
SHA256: f7f8b22e61ead3997c54b67d98fb97869f03e7868d26dbf463d813bc3c3351d8

import Definitions.Def_FairDivisionGraph_TreeMMS_Model

set_option autoImplicit false

noncomputable section

namespace FairDivisionGraph.TreeMMS

/-- Least part value. The artificial zero-player case is totalized by zero. -/
def partitionValue {m k : ℕ} (u : Fin m → ℝ) (P : Fin k → Finset (Fin m)) : ℝ := by
  classical
  let vals := Finset.univ.image (fun j => value u (P j))
  exact if h : vals.Nonempty then vals.min' h else 0

/-- The actual finite family of connected partitions, not a supplied optimum. -/
def partitions {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (k : ℕ) : Finset (Fin k → Finset (Fin m)) := by
  classical
  exact Finset.univ.filter (ConnectedPartition G V)

/-- Maximum of the finite family of least-part values. Zero when no partition exists.
For a tree with `1 ≤ k ≤ |V|`, the connected family is nonempty; this fact is not an input. -/
def mms {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (k : ℕ) (u : Fin m → ℝ) : ℝ := by
  classical
  let vals := (partitions G V k).image (partitionValue u)
  exact if h : vals.Nonempty then vals.max' h else 0

/-- The connected-partition MMS guarantee, with factor exactly one. -/
def IsMMS {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (π : Fin n → Finset (Fin m)) : Prop :=
  Valid G π ∧ ∀ i, mms G Finset.univ n (u i) ≤ value (u i) (π i)

end FairDivisionGraph.TreeMMS

MODULE: Grunbaum2003_ContainmentPolyTime
SHA256: 8b8c790af5ddc4d849e47bf332b28eb9b5d13131270d3243fb3914e48170dc87

import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

namespace Grunbaum2003

/-- Polynomial-time binary function. All stack alphabets are finite, including
internal stacks (a stronger finiteness condition than FinTM2 alone supplies). -/
def ContainmentPolyTime (f : List Bool → List Bool) : Prop :=
  ∃ M : Turing.TM2ComputableInPolyTime id id f, ∀ k, Finite (M.tm.Γ k)

end Grunbaum2003

MODULE: OptimalQueuingComplexity_Restless_encNat
SHA256: 5a1397565a8a0127a94c09139c1e15ecfc12bfd0953efeb73362209e2daa7f56

import Mathlib

namespace OptimalQueuingComplexity.Restless

/-- Self-delimiting binary numeral for a natural number `n`: the binary digits of `n`
(`Nat.bits n`, least significant first; empty for `n = 0`), each digit written twice, followed
by the terminator `01` (i.e. `[false, true]`). Its length is `2·(number of binary digits of n) + 2`,
so it is logarithmic in `n`. This is the length-faithful encoding used for every natural number
of an instance (never `Encodable`/`Nat.pair`, whose padding is exponential). -/
def encNat (n : ℕ) : List Bool :=
  (n.bits.flatMap fun b => [b, b]) ++ [false, true]

/-- An integer in sign-and-magnitude form: one sign bit (`true` iff negative), then the
magnitude as `encNat`. -/
def encInt (z : ℤ) : List Bool :=
  decide (z < 0) :: encNat z.natAbs

/-- A rational number as the pair (numerator, denominator) of its reduced form: `encInt` of the
numerator followed by `encNat` of the (positive) denominator. -/
def encRat (q : ℚ) : List Bool :=
  encInt q.num ++ encNat q.den

/-- An element `i` of `Fin n` as the binary numeral `encNat i`. -/
def encFin {n : ℕ} (i : Fin n) : List Bool := encNat i.val

/-- A table `f : Fin n → α` as the concatenation `e (f 0) ++ e (f 1) ++ …` of the encodings of
all its entries, in index order. The length `n` is not repeated here: every instance encoding writes
its dimensions first, so the table is self-delimiting in context. -/
def encTable {n : ℕ} {α : Type} (e : α → List Bool) (f : Fin n → α) : List Bool :=
  (List.finRange n).flatMap fun i => e (f i)

end OptimalQueuingComplexity.Restless

MODULE: Mathlib.Computability.TuringMachine.Computable (prefix)
SHA256: a5bf06eaaea6bd73a4493baf17fd9dd5e7c03ccf1ee96cbbb20e9f255c92c76f

/-
Copyright (c) 2020 Pim Spelier, Daan van Gent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pim Spelier, Daan van Gent
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Computability.Encoding
public import Mathlib.Computability.TuringMachine.StackTuringMachine

/-!
# Computable functions

This file contains the definition of a Turing machine with some finiteness conditions
(bundling the definition of TM2 in `StackTuringMachine.lean`), a definition of when a TM gives
a certain output (in a certain time), and the definition of computability (in polynomial time or
any time function) of a function between two types that have an encoding (as in `Encoding.lean`).

## Main theorems

- `idComputableInPolyTime` : a TM + a proof it computes the identity on a type in polytime.
- `idComputable`           : a TM + a proof it computes the identity on a type.

## Implementation notes

To count the execution time of a Turing machine, we have decided to count the number of times the
`step` function is used. Each step executes a statement (of type `Stmt`); this is a function, and
generally contains multiple "fundamental" steps (pushing, popping, and so on).
However, as functions only contain a finite number of executions and each one is executed at most
once, this execution time is up to multiplication by a constant the amount of fundamental steps.
-/

@[expose] public section



open Computability StateTransition


namespace Turing

/-- A bundled TM2 (an equivalent of the classical Turing machine, defined starting from
the namespace `Turing.TM2` in `StackTuringMachine.lean`), with an input and output stack,
a main function, an initial state and some finiteness guarantees. -/
structure FinTM2 where
  /-- index type of stacks -/
  {K : Type} [kDecidableEq : DecidableEq K]
  /-- A TM2 machine has finitely many stacks. -/
  [kFin : Fintype K]
  /-- input resp. output stack -/
  (k₀ k₁ : K)
  /-- type of stack elements -/
  (Γ : K → Type)
  /-- type of function labels -/
  (Λ : Type)
  /-- a main function: the initial function that is executed, given by its label -/
  (main : Λ)
  /-- A TM2 machine has finitely many function labels. -/
  [ΛFin : Fintype Λ]
  /-- type of states of the machine -/
  (σ : Type)
  /-- the initial state of the machine -/
  (initialState : σ)
  /-- a TM2 machine has finitely many internal states. -/
  [σFin : Fintype σ]
  /-- Each internal stack is finite. -/
  [Γk₀Fin : Fintype (Γ k₀)]
  /-- the program itself, i.e. one function for every function label -/
  (m : Λ → Turing.TM2.Stmt Γ Λ σ)

attribute [nolint docBlame] FinTM2.kDecidableEq

namespace FinTM2

section

variable (tm : FinTM2)

instance decidableEqK : DecidableEq tm.K :=
  tm.kDecidableEq

instance inhabitedσ : Inhabited tm.σ :=
  ⟨tm.initialState⟩

/-- The type of statements (functions) corresponding to this TM. -/
def Stmt : Type :=
  Turing.TM2.Stmt tm.Γ tm.Λ tm.σ

instance inhabitedStmt : Inhabited (Stmt tm) :=
  inferInstanceAs (Inhabited (Turing.TM2.Stmt tm.Γ tm.Λ tm.σ))

/-- The type of configurations (functions) corresponding to this TM. -/
def Cfg : Type :=
  Turing.TM2.Cfg tm.Γ tm.Λ tm.σ

instance inhabitedCfg : Inhabited (Cfg tm) :=
  Turing.TM2.Cfg.inhabited _ _ _

/-- The step function corresponding to this TM. -/
@[simp]
def step : tm.Cfg → Option tm.Cfg :=
  Turing.TM2.step tm.m

end

end FinTM2

/-- The initial configuration corresponding to a list in the input alphabet. -/
def initList (tm : FinTM2) (s : List (tm.Γ tm.k₀)) : tm.Cfg where
  l := Option.some tm.main
  var := tm.initialState
  stk k :=
    @dite (List (tm.Γ k)) (k = tm.k₀) (tm.kDecidableEq k tm.k₀) (fun h => by rw [h]; exact s)
      fun _ => []

/-- The final configuration corresponding to a list in the output alphabet. -/
def haltList (tm : FinTM2) (s : List (tm.Γ tm.k₁)) : tm.Cfg where
  l := Option.none
  var := tm.initialState
  stk k :=
    @dite (List (tm.Γ k)) (k = tm.k₁) (tm.kDecidableEq k tm.k₁) (fun h => by rw [h]; exact s)
      fun _ => []

@[deprecated (since := "2026-03-06")] protected alias EvalsTo :=
  StateTransition.EvalsTo
@[deprecated (since := "2026-03-06")] protected alias EvalsToInTime :=
  StateTransition.EvalsToInTime

/-- A proof of tm outputting l' when given l. -/
def TM2Outputs (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁))) :=
  EvalsTo tm.step (initList tm l) ((Option.map (haltList tm)) l')

/-- A proof of tm outputting l' when given l in at most m steps. -/
def TM2OutputsInTime (tm : FinTM2) (l : List (tm.Γ tm.k₀)) (l' : Option (List (tm.Γ tm.k₁)))
    (m : ℕ) :=
  EvalsToInTime tm.step (initList tm l) ((Option.map (haltList tm)) l') m

/-- The forgetful map, forgetting the upper bound on the number of steps. -/
def TM2OutputsInTime.toTM2Outputs {tm : FinTM2} {l : List (tm.Γ tm.k₀)}
    {l' : Option (List (tm.Γ tm.k₁))} {m : ℕ} (h : TM2OutputsInTime tm l l' m) :
    TM2Outputs tm l l' :=
  h.toEvalsTo

/-- A (bundled TM2) Turing machine
with input alphabet equivalent to `Γ₀` and output alphabet equivalent to `Γ₁`. -/
structure TM2ComputableAux (Γ₀ Γ₁ : Type) where
  /-- the underlying bundled TM2 -/
  tm : FinTM2
  /-- the input alphabet is equivalent to `Γ₀` -/
  inputAlphabet : tm.Γ tm.k₀ ≃ Γ₀
  /-- the output alphabet is equivalent to `Γ₁` -/
  outputAlphabet : tm.Γ tm.k₁ ≃ Γ₁

/-- A Turing machine + a proof it outputs `f`. -/
structure TM2Computable {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β) extends
  TM2ComputableAux αΓ βΓ where
  /-- a proof this machine outputs `f` -/
  outputsFun :
    ∀ a,
      TM2Outputs tm (List.map inputAlphabet.invFun (ea a))
        (Option.some ((List.map outputAlphabet.invFun) (eb (f a))))

/-- A Turing machine + a time function +
a proof it outputs `f` in at most `time(input.length)` steps. -/
structure TM2ComputableInTime {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
  (f : α → β) extends TM2ComputableAux αΓ βΓ where
  /-- a time function -/
  time : ℕ → ℕ
  /-- proof this machine outputs `f` in at most `time(input.length)` steps -/
  outputsFun :
    ∀ a,
      TM2OutputsInTime tm (List.map inputAlphabet.invFun (ea a))
        (Option.some ((List.map outputAlphabet.invFun) (eb (f a))))
        (time (ea a).length)

/-- A Turing machine + a polynomial time function +
a proof it outputs `f` in at most `time(input.length)` steps. -/
structure TM2ComputableInPolyTime {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ)
  (f : α → β) extends TM2ComputableAux αΓ βΓ where
  /-- a polynomial time function -/
  time : Polynomial ℕ
  /-- proof that this machine outputs `f` in at most `time(input.length)` steps -/
  outputsFun :
    ∀ a,
      TM2OutputsInTime tm (List.map inputAlphabet.invFun (ea a))
        (Option.some ((List.map outputAlphabet.invFun) (eb (f a))))
        (time.eval (ea a).length)


MODULE: Encoding
SHA256: 47a436a245224bc5b8ca6fd195e29b195b22222b008fbbb2673f761ec580311e

import Definitions.Def_FairDivisionGraph_TreeMMS_MMS
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat
import Definitions.Def_Grunbaum2003_ContainmentPolyTime
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

set_option autoImplicit false

namespace FairDivisionGraph.TreeMMS

open OptimalQueuingComplexity.Restless

/-- Concrete rational input data; graph and utilities are inputs, not a witness allocation. -/
structure RationalInput where
  m : ℕ
  n : ℕ
  adj : Fin m → Fin m → Bool
  utility : Fin n → Fin m → ℚ

/-- Symmetric loop-free interpretation of a Boolean matrix. Well-formed inputs
already have both properties, so the interpretation changes no edge. -/
def RationalInput.graph (I : RationalInput) : SimpleGraph (Fin I.m) where
  Adj v w := v ≠ w ∧ I.adj v w = true ∧ I.adj w v = true
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (I : RationalInput) : DecidableRel I.graph.Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ _ = true ∧ _ = true))

/-- Initial rational CFD conditions, without any positivity condition on individual entries. -/
def RationalInput.WellFormed (I : RationalInput) : Prop :=
  0 < I.n ∧ I.n ≤ I.m ∧
  (∀ v, I.adj v v = false) ∧ (∀ v w, I.adj v w = I.adj w v) ∧
  (∀ i v, 0 ≤ I.utility i v) ∧ (∀ i, ∑ v, I.utility i v = 1)

instance (I : RationalInput) : Decidable I.WellFormed := by
  unfold RationalInput.WellFormed
  infer_instance

/-- Coordinatewise inclusion of rational utilities in the real existence model. -/
def RationalInput.realUtility (I : RationalInput) : Fin I.n → Fin I.m → ℝ :=
  fun i v => (I.utility i v : ℝ)

/-- Dimensions in self-delimiting binary, then adjacency bits and the rational utility table. -/
def encodeInput (I : RationalInput) : List Bool :=
  encNat I.m ++ encNat I.n ++
  encTable (fun row => encTable (fun b => [b]) row) I.adj ++
  encTable (fun row => encTable encRat row) I.utility

/-- Read the doubled-bit natural code; noncanonical representations are rejected by input decoding. -/
def readNat : List Bool → Option (ℕ × List Bool)
  | false :: true :: xs => some (0, xs)
  | b :: c :: xs => if b = c then do
      let (n, rest) ← readNat xs
      return (Nat.bit b n, rest)
    else none
  | _ => none

/-- Read one bit. -/
def readBit : List Bool → Option (Bool × List Bool)
  | b :: xs => some (b, xs)
  | [] => none

/-- Read a signed numerator and a strictly positive denominator. -/
def readRat (xs : List Bool) : Option (ℚ × List Bool) := do
  let (negative, xs) ← readBit xs
  let (a, xs) ← readNat xs
  let (d, xs) ← readNat xs
  if d = 0 then none else
    let z : ℤ := if negative then -(a : ℤ) else (a : ℤ)
    return ((z : ℚ) / (d : ℚ), xs)

/-- Read a table of its specified length, in index order. -/
def readTable {α : Type} (read : List Bool → Option (α × List Bool)) :
    (k : ℕ) → List Bool → Option ((Fin k → α) × List Bool)
  | 0, xs => some (Fin.elim0, xs)
  | k + 1, xs => do
      let (a, xs) ← read xs
      let (f, xs) ← readTable read k xs
      return (Fin.cases a f, xs)

/-- Syntactic decoder: dimensions are bounded by word length before allocating tables.
Canonical encodings have these bounds. No trailing bits or noncanonical number codes pass. -/
def decodeInput (word : List Bool) : Option RationalInput := do
  let (m, xs) ← readNat word
  let (n, xs) ← readNat xs
  if m > word.length ∨ n > word.length then none else do
    let (adj, xs) ← readTable (readTable readBit m) m xs
    let (u, xs) ← readTable (readTable readRat m) n xs
    let I : RationalInput := ⟨m, n, adj, u⟩
    if xs = [] ∧ encodeInput I = word then some I else none

/-- Finite exact validity test for rational tree inputs. For a finite simple graph,
connectedness and `|E| + 1 = |V|` are the tree criterion. -/
def validTreeInput (I : RationalInput) : Bool :=
  decide (I.WellFormed ∧ I.graph.Connected ∧ I.graph.edgeFinset.card + 1 = I.m)

/-- Reject syntactically malformed or mathematically invalid inputs explicitly. -/
def decodeTreeInput (word : List Bool) : Option RationalInput := do
  let I ← decodeInput word
  if validTreeInput I then some I else none

/-- Output: a success bit and one incidence row per agent. An error is `[false]`. -/
def encodeAllocation {m n : ℕ} (π : Fin n → Finset (Fin m)) : List Bool :=
  true :: encTable (fun S => encTable (fun v => [decide (v ∈ S)]) (fun v : Fin m => v)) π

/-- Decode exactly `n*m` incidence bits following a success bit. No completeness is imposed. -/
def decodeAllocation (m n : ℕ) (word : List Bool) : Option (Fin n → Finset (Fin m)) := do
  let (success, xs) ← readBit word
  if !success then none else do
    let (a, xs) ← readTable (readTable readBit m) n xs
    if xs = [] then
      some (fun i => Finset.univ.filter (fun v => a i v = true))
    else none

/-- Exact rational output uses a success bit and the shared rational code. -/
def encodeValue (q : ℚ) : List Bool := true :: encRat q

/-- Exact rational output decoder, rejecting errors, zero denominators and trailing data. -/
def decodeValue (word : List Bool) : Option ℚ := do
  let (success, xs) ← readBit word
  if !success then none else do
    let (q, xs) ← readRat xs
    if xs = [] then some q else none

/-- Threshold input contains the ordinary instance and all threshold bit strings. -/
def encodeThresholds (I : RationalInput) (q : Fin I.n → ℚ) : List Bool :=
  encodeInput I ++ encTable encRat q

/-- The selected player's index is included in exact MMS computation input. -/
def encodePlayer (I : RationalInput) (i : Fin I.n) : List Bool :=
  encodeInput I ++ encFin i

/-- Allocation-solving relation for the main theorem. Only valid tree inputs are promised. -/
def SolvesMMS (f : List Bool → List Bool) : Prop :=
  ∀ I : RationalInput, I.WellFormed → I.graph.IsTree →
    ∃ π, decodeAllocation I.m I.n (f (encodeInput I)) = some π ∧
      IsMMS I.graph I.realUtility π

/-- Exact threshold solving, with arbitrary rational thresholds including nonpositive ones. -/
def SolvesThresholds (f : List Bool → List Bool) : Prop :=
  ∀ (I : RationalInput) (q : Fin I.n → ℚ), I.WellFormed → I.graph.IsTree →
    (∀ i, (q i : ℝ) ≤ mms I.graph Finset.univ I.n (I.realUtility i)) →
    ∃ π, decodeAllocation I.m I.n (f (encodeThresholds I q)) = some π ∧
      Valid I.graph π ∧ ∀ i, (q i : ℝ) ≤ value (I.realUtility i) (π i)

/-- Exact MMS value computation, with no error tolerance or supplied MMS values. -/
def ComputesMMS (f : List Bool → List Bool) : Prop :=
  ∀ (I : RationalInput) (i : Fin I.n), I.WellFormed → I.graph.IsTree →
    ∃ q : ℚ, decodeValue (f (encodePlayer I i)) = some q ∧
      (q : ℝ) = mms I.graph Finset.univ I.n (I.realUtility i)

end FairDivisionGraph.TreeMMS

END IMPORTED DEPENDENCY SOURCE
-/
