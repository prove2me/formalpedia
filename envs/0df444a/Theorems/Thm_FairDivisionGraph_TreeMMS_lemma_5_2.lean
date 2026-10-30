-- Prove2me | Theorems.Thm_FairDivisionGraph_TreeMMS_lemma_5_2
-- name    : FairDivisionGraph.TreeMMS.lemma_5_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:20:48.717337+00:00
-- url     : https://prove2.me/theorems/1ac95fc3-862a-4140-a62c-6a47728e8ebd
-- title:
--   Lemma 5.2 — remaining players retain their original thresholds
-- statement:
--   Let $G$ be a finite tree on $m$ vertices and let $u$ be normalized, nonnegative real utilities for $1\le n\le m$ agents. Let $q_i\in\mathbb Q$ be arbitrary thresholds with $q_i\le\operatorname{mms}_i(I)$ for every agent. Follow any finite prefix of Algorithm 1's recursive calls, using the displayed universal child condition and any legal choices. If $V'$ and $N'$ are the remaining vertices and agents, then
--   $$\operatorname{mms}(G,V',|N'|,u_j)\ge q_j\qquad(j\in N').$$
--   Utilities in this expression are restricted, never renormalized. The conclusion concerns the actual reached states, including the initial state and any state that could subsequently fail; successful execution is not a hypothesis. This is the residual threshold invariant used by Proposition 5.1.
--
--   Differences from the source:
--   - encoding: finite vertex and player sets, with players numbered 1 through n → vertices Fin m and agents Fin n, both zero-based; reason: finite relabelling changes no instance
--   - encoding: the standing CFD assumptions of §2 → IsCFD explicitly includes positive player count, n ≤ m, nonnegativity and normalization; reason: these are the source assumptions and the nonempty-player convention implicit in its minimum
--   - encoding: valid allocations and connected partitions → valid bundles may be empty; partition parts are nonempty; MMS is a finite maximum totalized by zero outside its meaningful domain; reason: the empty allocation is expressly permitted and tree partitions exist throughout the theorem domain
--   - encoding: the recursively constructed instances I_k with |N_k| = k → every state reached by finite prefixes of Algorithm 1 local transitions, indexed by its remaining-agent cardinality; reason: restores the preceding paragraph without assuming successful execution or the invariant
--   - encoding: the restriction u_j to residual vertices → original utility functions summed only over residual vertices and parts; reason: preserves original numerical thresholds without renormalization
--   - encoding: Algorithm 1 root and vertex choices → any root and choice satisfying the universal-over-players child test; reason: represents exactly the displayed local rule and all its tie breaks
-- source:
--   Bouveret, Cechlárová, Elkind, Igarashi and Peters (2017), Fair Division of a Graph, IJCAI-17, https://doi.org/10.24963/ijcai.2017/20, Lemma 5.2, printed p. 139 (PDF p. 5)

import Definitions.Def_FairDivisionGraph_TreeMMS_Algorithm

set_option autoImplicit false

namespace FairDivisionGraph.TreeMMS

/-- Lemma 5.2, applied to every reached residual state, including prefixes of failing executions. -/
theorem lemma_5_2 {m n : ℕ} (G : SimpleGraph (Fin m))
    (u : Fin n → Fin m → ℝ) (q : Fin n → ℚ)
    (hCFD : IsCFD u) (hTree : G.IsTree)
    (hq : ∀ i, (q i : ℝ) ≤ mms G Finset.univ n (u i))
    (s : Residual m n) (hs : Reached G u q s) :
    ∀ j ∈ s.agents, (q j : ℝ) ≤ mms G s.vertices s.agents.card (u j) := by sorry

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

MODULE: Algorithm
SHA256: b52a7ec725911344e619f0239dd29e21d72c29c9ab5639645f01b12df1bfe180

import Definitions.Def_FairDivisionGraph_TreeMMS_MMS

set_option autoImplicit false

noncomputable section

namespace FairDivisionGraph.TreeMMS

/-- Residual labels retain their original names and original utilities. -/
structure Residual (m n : ℕ) where
  vertices : Finset (Fin m)
  agents : Finset (Fin n)

/-- The initial recursive state. -/
def initial (m n : ℕ) : Residual m n := ⟨Finset.univ, Finset.univ⟩

/-- Descendants include `v`: the simple root-to-vertex path passes through `v`.
On a tree the simple path is unique. -/
def descendants {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (r v : Fin m) : Finset (Fin m) := by
  classical
  exact V.filter fun x => ∃ (hr : r ∈ V) (hx : x ∈ V),
    ∃ p : (G.induce (V : Set (Fin m))).Walk ⟨r, hr⟩ ⟨x, hx⟩,
      p.IsPath ∧ v ∈ p.support.map Subtype.val

/-- A child is an adjacent strict descendant, in the induced residual tree. -/
def Child {m : ℕ} (G : SimpleGraph (Fin m)) (V : Finset (Fin m))
    (r v w : Fin m) : Prop :=
  G.Adj v w ∧ w ∈ descendants G V r v ∧ w ≠ v

/-- The explicit line 1 failure test. -/
def Shortfall {m n : ℕ} (u : Fin n → Fin m → ℝ) (q : Fin n → ℚ)
    (s : Residual m n) : Prop :=
  ∃ i ∈ s.agents, value (u i) s.vertices < (q i : ℝ)

/-- Exactly the local root and line-7 choice guards, universal over remaining players. -/
def Eligible {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (s : Residual m n) (r v : Fin m) (i : Fin n) : Prop :=
  r ∈ s.vertices ∧ v ∈ s.vertices ∧ i ∈ s.agents ∧
  (q i : ℝ) ≤ value (u i) (descendants G s.vertices r v) ∧
  ∀ w, Child G s.vertices r v w →
    ∀ j ∈ s.agents, value (u j) (descendants G s.vertices r w) < (q j : ℝ)

/-- Delete the selected bundle and player; utilities are never rescaled. -/
def remove {m n : ℕ} (G : SimpleGraph (Fin m)) (s : Residual m n)
    (r v : Fin m) (i : Fin n) : Residual m n :=
  ⟨s.vertices \ descendants G s.vertices r v, s.agents.erase i⟩

/-- A recursive call is made precisely when these local guards hold. -/
def Recurses {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (s t : Residual m n) : Prop :=
  ¬ Shortfall u q s ∧ 1 < s.agents.card ∧
  ∃ r v i, Eligible G u q s r v i ∧ t = remove G s r v i

/-- All states actually reached by finite prefixes, including states that subsequently fail.
No successful return or residual MMS invariant is assumed. -/
def Reached {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (s : Residual m n) : Prop :=
  Relation.ReflTransGen (Recurses G u q) (initial m n) s

/-- Failure also represents an absent choice or the undefined zero-player input. -/
def FailsHere {m n : ℕ} (G : SimpleGraph (Fin m)) (u : Fin n → Fin m → ℝ)
    (q : Fin n → ℚ) (s : Residual m n) : Prop :=
  Shortfall u q s ∨ s.agents.card = 0 ∨
    (1 < s.agents.card ∧ ¬ ∃ r v i, Eligible G u q s r v i)

/-- Relational execution of Algorithm 1, allowing every legal root and tie break.
The recursive result is evaluated once and reused; `none` propagates failure. -/
inductive Execution {m n : ℕ} (G : SimpleGraph (Fin m))
    (u : Fin n → Fin m → ℝ) (q : Fin n → ℚ) :
    Residual m n → Option (Fin n → Finset (Fin m)) → Prop
  | fail (s) : FailsHere G u q s → Execution G u q s none
  | single (s) : ¬ Shortfall u q s → s.agents.card = 1 →
      Execution G u q s (some (fun i => if i ∈ s.agents then s.vertices else ∅))
  | recurse (s) (r v) (i) (out) : ¬ Shortfall u q s → 1 < s.agents.card →
      Eligible G u q s r v i → Execution G u q (remove G s r v i) out →
      Execution G u q s (out.map (fun π => Function.update π i (descendants G s.vertices r v)))

end FairDivisionGraph.TreeMMS

END IMPORTED DEPENDENCY SOURCE
-/
