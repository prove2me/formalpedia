-- Prove2me | Theorems.Thm_EuclidKSteiner_lemma_4_4
-- name    : EuclidKSteiner.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:20:10.14477+00:00
-- url     : https://prove2.me/theorems/abde20e7-f586-41dd-9d9c-eac077ab45c5
-- title:
--   Lemma 4.4 — a realization yields a tree of weight $\le w(M)+w-\Phi(A)$, constructed in $(|G|+b)^{O(1)}$ time
-- statement:
--   Work in the graph setting. Let a realization of a template for $(b,k)$ have cost $w$, terminal-image set $A$ and candidate-image set $S$.
--
--   1. There is a tree in $G$ with vertex set $P\cup S$ of weight at most $w(M)+w-\Phi(A)$, with at most $b$ Steiner edges, and $|S|\le k$.
--   2. There are a deterministic real-RAM program and a constant $C>0$ such that, given the graph (vertices $0,\dots,|V|-1$, terminal flags, edge list with weights), $b$, $k$, the template and its realization, the program halts within $C(|V|+|E|+b+2)^C$ steps and outputs the edge list of such a tree.
--
--   The lemma turns the best realization found by the dynamic program into an actual solution.
--
--   **Formalization Note** The tree $M$ is not part of the input; the bound is with respect to the fixed $M$ of the setting, and $w(M)$ and $\Phi$ do not depend on which minimum spanning tree of $G[P]$ is fixed.
--
--   Differences from the source:
--   - encoding: graph G with nonnegative edge weights, terminals P, candidates Q = V(G) \ P, G[P] connected, a fixed minimum spanning tree M of G[P], |P| ≥ 2 (§3 preamble) → the fields of GraphSetting; the existence of the minimum spanning tree M of G[P] encodes connectivity; reason: the standing assumptions of §§3–4, stated once
--   - encoding: a tree in G with vertex set P ∪ S → a spanning tree of P ∪ S using edges of G; reason: the same object
--   - encoding: constructed deterministically in (|G| + b)^{O(1)} time on the real RAM, given the template and its realization → an admissible MatMulTimeLP.RealRAM program and C > 0 fixed before the input, halting with t + 1 ≤ C·(|V| + |E| + b + 2)^C on realizationLayout and outputting an edge list without repetition of such a tree; reason: O-notation with constants before the input; |G| = |V| + |E|; +2 keeps the base at least 2
-- source:
--   Bhore, Kisfaludi-Bak, Marx, Odak, Parameterized Tractability of Euclidean k-Steiner Tree, STOC 2027 submission (manuscript sha256 75361687…), Lemma 4.4, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_FewInnerTSP_Admissible
import Definitions.Def_EuclidKSteiner_Layouts

namespace EuclidKSteiner

open Classical in
/-- **Lemma 4.4 (From a template realization to a solution).** Bhore, Kisfaludi-Bak, Marx, Odak,
*Parameterized Tractability of Euclidean k-Steiner Tree*, STOC 2027 submission (manuscript sha256
75361687…), Lemma 4.4, p.17 (PDF p.19): "Let a template realization have cost w, terminal-image set
A, and candidate-image set S. There is a tree in G with vertex set P ∪ S of weight at most
w(M) + w − Φ(A), with at most b Steiner edges and |S| ≤ k. Given the template and its realization,
such a tree can be constructed deterministically in (|G| + b)^{O(1)} time on the real RAM."

1. (Existence.) In the graph setting, for every template `T` for `(b, k)` and every realization `φ`
   of `T` with cost `w`, terminal-image set `A` and candidate-image set `S`, there is a spanning tree
   of `P ∪ S` in `G` of weight at most `w(M) + w − Φ(A)` with at most `b` Steiner edges, and
   `|S| ≤ k`.
2. (Construction.) There are an admissible real-RAM program and `C > 0` such that, on every graph
   `G` on `{0, …, |V| − 1}` (in the graph setting), every listing of its edges, every template for
   `(b, k)` and every realization, given in the layout `realizationLayout`, the run halts at a step
   `t` with `t + 1 ≤ C·(|V| + |E| + b + 2)^C` and outputs an edge list (without repetition) of such a
   tree.

**Formalization Note** `M` is not part of the input ("including computing M if necessary"); the
statement holds for the fixed `M` of the setting, and `w(M)` and `Φ` do not depend on which minimum
spanning tree of `G[P]` is fixed. `|G| = |V| + |E|`. -/
theorem lemma_4_4 :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (S : GraphSetting V) (b k : ℕ) (T : Template),
      T.IsTemplateFor b k → ∀ φ : ℕ → V, S.IsRealization T φ →
        ∃ Tr : Finset (Sym2 V),
          IsSpanningTree (S.P ∪ GraphSetting.candImages T (Finset.range T.size) φ) id S.E Tr ∧
          edgeSum S.w Tr ≤
            edgeSum S.w S.M + S.realCost T φ - S.Phi (GraphSetting.termImages T (Finset.range T.size) φ) ∧
          (Tr.filter (fun e => ∃ v ∈ e, v ∉ S.P)).card ≤ b ∧
          (GraphSetting.candImages T (Finset.range T.size) φ).card ≤ k) ∧
    ∃ A : MatMulTimeLP.Program, FewInnerTSP.Admissible A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (nV : ℕ) (S : GraphSetting (Fin nV)) (Ls : List (Fin nV × Fin nV)), IsEdgeListing Ls S.E →
      ∀ (b k : ℕ) (T : Template), T.IsTemplateFor b k →
      ∀ φ : ℕ → Fin nV, S.IsRealization T φ → ∀ ω : MatMulTimeLP.Tape,
        ∃ t : ℕ, MatMulTimeLP.HaltsAt A (realizationLayout S Ls b k T φ) ω t ∧
          (t : ℝ) + 1 ≤ C * ((nV : ℝ) + Ls.length + b + 2) ^ C ∧
          ∃ L : List (Fin nV × Fin nV),
            OutputIs A (realizationLayout S Ls b k T φ) ω t (encodeEdgeList L) ∧
            ∃ Tr : Finset (Sym2 (Fin nV)), IsEdgeListing L Tr ∧
              IsSpanningTree (S.P ∪ GraphSetting.candImages T (Finset.range T.size) φ) id S.E Tr ∧
              edgeSum S.w Tr ≤
                edgeSum S.w S.M + S.realCost T φ - S.Phi (GraphSetting.termImages T (Finset.range T.size) φ) ∧
              (Tr.filter (fun e => ∃ v ∈ e, v ∉ S.P)).card ≤ b ∧
              (GraphSetting.candImages T (Finset.range T.size) φ).card ≤ k := by sorry

end EuclidKSteiner
