-- Prove2me | Theorems.Thm_DynOracleConn_gadget_isAcyclic
-- name    : DynOracleConn.gadget_isAcyclic
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:51:50.059705+00:00
-- url     : https://prove2.me/theorems/205173c4-1abd-4944-8175-104b34251449
-- title:
--   §3.1, p.20 — $\mathcal G_n(\pi,z)$ has degree at most 2 and is two disjoint paths plus isolated vertices; adding $\{t,v^0_i\}$ keeps a forest
-- statement:
--   Let $\mathcal G_n(\pi,z)$ be the graph of §3.1, placed on $[n]$ by an injection of the named vertices. Then:
--
--   1. every vertex has degree at most $2$;
--   2. $\mathcal G_n(\pi,z)$ is a forest;
--   3. $t$ is isolated;
--   4. every vertex outside the named vertices is isolated;
--   5. if $d\ge1$, then $s$ and $l^1_1$ lie in different components, and every named vertex other than $t$ is connected to one of them;
--   6. for every item $i$, the graph $\mathcal G_n(\pi,z)+\{t,v^0_i\}$ is a forest.
--
--   Clauses 1 to 5 express that, apart from isolated vertices, the edges form two vertex-disjoint paths. Clause 6 gives the forest property of the graphs during an epoch, which Theorem 4 needs.
--
--   Differences from the source:
--   - encoding: [d] 1-based → Fin d, 0-based; reason: Lean convention; same instances
--   - generalization: d = ⌊(n−2)/8⌋ and one vertex layout → any injection e of the named vertices into Fin n; reason: the paper's layout is one such injection
--   - encoding: the edges form two vertex-disjoint paths → forest, degree at most 2, two components covering the named vertices other than t; reason: a forest of maximum degree 2 is a union of paths; same structure
--   - generalization: the paragraph on p.20 describes the graph without the epoch edge → an added clause: adding {t, v⁰ᵢ} keeps a forest; reason: it extends the statement and contains the printed one; the forest claim of Theorem 4 needs it
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), §3.1, p.20

import Mathlib
import Definitions.Def_DynOracleConn_Gadget

namespace DynOracleConn

/-- **§3.1, p.20 — the structure of 𝒢ₙ(π, z).** Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), §3.1, p.20:
"Every vertex has degree at most 2. Apart from the isolated vertices t and D, the edges form two
vertex-disjoint paths: path 0, which contains s, and path 1, which contains l¹₁ (see Figure 3)."
The epoch graphs of §3.1.1 add one edge `{t, v⁰ᵢ}` at a time; they stay forests.

For every injection `e` of the named vertices into `Fin n` and every instance `X = (π, z)`:
1. every vertex has at most two neighbors;
2. 𝒢ₙ(π, z) is a forest;
3. `t` and every vertex of `D` (outside the range of `e`) are isolated;
4. if `d ≥ 1`, `s` and `l¹₀` (the paper's `l¹₁`) lie in different components, and every named
   vertex other than `t` is connected to one of them (the two paths);
5. adding `{t, v⁰ᵢ}` for any item `i` keeps the graph a forest.

**Formalization Note.** Slots are 0-based, so the paper's `l¹₁` is `GV.l true ⟨0, h⟩`. -/
theorem gadget_isAcyclic {n d : ℕ} (e : GV d ↪ Fin n) (X : PPHPInst d) :
    (∀ a : Fin n, ((gadget e X).neighborSet a).ncard ≤ 2) ∧
    (gadget e X).IsAcyclic ∧
    (∀ w : Fin n, ¬ (gadget e X).Adj (e GV.t) w) ∧
    (∀ a : Fin n, a ∉ Set.range e → ∀ w : Fin n, ¬ (gadget e X).Adj a w) ∧
    (∀ h : 0 < d, ¬ (gadget e X).Reachable (e GV.s) (e (GV.l true ⟨0, h⟩)) ∧
      ∀ x : GV d, x ≠ GV.t →
        (gadget e X).Reachable (e GV.s) (e x) ∨ (gadget e X).Reachable (e (GV.l true ⟨0, h⟩)) (e x)) ∧
    (∀ i : Fin d, (withT e X i).IsAcyclic) := by sorry

end DynOracleConn
