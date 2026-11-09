-- Prove2me | Theorems.Thm_BinaryThreeLCC_Main_transition_graph_properties
-- name    : BinaryThreeLCC.Main.transition_graph_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:02:52.956392+00:00
-- url     : https://prove2.me/theorems/5fcf4b0a-8688-4223-a203-4b6d9b9813b5
-- title:
--   Proposition 5.5 — all transition graph properties
-- statement:
--   Let $\Omega,\Lambda$ have sizes $m\ge2,n\ge1$. Let $\mathcal H$ be a distinct-pair tuple system unique at each $(u,a)$ whose flattening is Eulerian and $\lambda$-cut-dense for $\lambda>0$. Construct $\mathcal T$ with its real tuples and fake copies, and let $Q_{\mathcal T}(u',u)$ count directed tuple copies. Forgetting their directions gives the undirected graph with adjacency $A_{\mathcal T}=Q_{\mathcal T}+Q_{\mathcal T}^{\mathsf T}$. All five source conclusions hold:
--
--   1. Every flattening edge appears at least twice in $D_{\mathcal T}$, expressed as the corresponding multiplicity inequality for every ordered endpoint pair.
--   2. $D_{\mathcal T}$ is Eulerian, both degrees at every vertex are $2n$, and at least $n$ of its edges there are loops.
--   3. The undirected graph is $4n$-regular.
--   4. With $M_a(u',u)=\tfrac12|\{(u,a,\star,u')\in\mathcal T\}|$,
--
--   $$\mathbb E_{a\in\Lambda}M_a=\frac{Q_{\mathcal T}}{2n},\qquad
--   \sum_{u'}M_a(u',u)=1,\qquad M_a(u,u)\ge\frac12.$$
--
--   5. For the second smallest Laplacian eigenvalue, counted with multiplicity,
--
--   $$\lambda_2\left(I-\frac{A_{\mathcal T}}{4n}\right)\ge\frac{\lambda^2m^2}{8n^2}.$$
--
--   No connectivity assumption is imposed independently of positive cut density.
--
--   Differences from the source:
--   - encoding: finite sets with one-based indices → finite types and zero-based Fin indices; reason: a change of enumeration preserves every vertex, coordinate and edge copy
--   - reading: Section 3 allows loops but Definition 3.1 writes two-element edges → labelled endpoint pairs, loops of length one, parallel-edge cycles of length two, and loops counted twice in undirected degrees and adjacency; reason: the standing multigraph convention and A_T = Q_T + Q_T transpose control the interpretation
--   - encoding: the literal second eigenvalue in clause (5) → m ≥ 2 and n ≥ 1, positive expansion, and the published Hermitian eigenvalue list with multiplicity; reason: the spectral entry and normalization are then defined; the singleton dimension case is handled directly in Lemma 4.1
--   - generalization: the surrounding tuple construction also has parity vector labels → no vector labels or parity hypotheses in the transition-graph properties; reason: all five clauses concern the tuple counts alone
-- source:
--   Oliver Janzer, Peter Manohar, STOC 2027 submission #732 (October 2026), Proposition 5.5, printed p. 14, PDF p. 16; clauses (3)–(5) continue on printed p.15, PDF p.17; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf

import Definitions.Def_BinaryThreeLCC_Main_TupleSystem
import Definitions.Def_BinaryThreeLCC_Main_Spectral

set_option autoImplicit false

namespace BinaryThreeLCC.Main

/-- Proposition 5.5, all five clauses. Its spectral clause has m ≥ 2. -/
theorem transition_graph_properties {Ω Λ : Type} [Fintype Ω] [DecidableEq Ω]
    [Fintype Λ] [Nonempty Λ] (hm : 2 ≤ Fintype.card Ω)
    (H : TupleSystem Ω Λ) (lam : ℝ) (hlam : 0 < lam)
    (hEuler : Eulerian (tupleGraph H)) (hcut : CutDense (tupleGraph H) lam) :
    (∀ u v : Ω,
      2 * (((H.tuples.filter (fun t => t.1 = u ∧ t.2.2 = v)).card : ℕ) : ℝ) ≤
        transitionQ H v u) ∧
    (Eulerian (transitionGraph H) ∧
      ∀ u, inDegree (transitionGraph H) u = 2 * Fintype.card Λ ∧
        outDegree (transitionGraph H) u = 2 * Fintype.card Λ ∧
        (Fintype.card Λ : ℝ) ≤ transitionQ H u u) ∧
    (∀ u, (transitionGraph H).deg u = 4 * Fintype.card Λ) ∧
    ((∀ u v, average (fun a : Λ => transitionM H a v u) =
        transitionQ H v u / (2 * (Fintype.card Λ : ℝ))) ∧
      (∀ a : Λ, ∀ u, ∑ v, transitionM H a v u = 1) ∧
      ∀ a : Λ, ∀ u, (1 / 2 : ℝ) ≤ transitionM H a u u) ∧
    lam ^ 2 * (Fintype.card Ω : ℝ) ^ 2 / (8 * (Fintype.card Λ : ℝ) ^ 2) ≤
      secondSmallest (normalizedLaplacian (transitionGraph H) (4 * (Fintype.card Λ : ℝ))) := by sorry

end BinaryThreeLCC.Main
