-- Prove2me | Theorems.Thm_BayesGroupHard_VertexCover_fact_1
-- name    : BayesGroupHard.VertexCover.fact_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:32.375982+00:00
-- url     : https://prove2.me/theorems/a22754a0-a556-42bb-99c5-6a55cfbe067c
-- title:
--   Fact 1, p. 28 — an edge agent announces 1 at time one iff one of its two vertex agents has signal 1
-- statement:
--   In the vertex-cover network of a graph $G$ (for any parameters $k_0, k_1$ of agent $\kappa$), let $\varepsilon$ be the edge agent of the edge $e = \{\varepsilon^{(1)}, \varepsilon^{(2)}\}$. On every signal profile $s$,
--   $$a_{\varepsilon,1} = \mathbf 1\{ s_{\varepsilon^{(1)}} = 1 \text{ or } s_{\varepsilon^{(2)}} = 1 \}.$$
--
--   This is the gadget of the reduction: at time one each edge agent reports whether its edge is covered by the set of vertex agents with signal $1$.
--
--   **Formalization Note.** Stated as: `act (vcNet G k₀ k₁) 1 (edg e) s = true` iff some endpoint `v ∈ e` has `s (vtx v) = true`. Edge agents do not observe $\kappa$, so no hypothesis on $k_0, k_1$ is needed.
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, p. 28, Fact 1

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Model

open Finset

namespace BayesGroupHard.VertexCover

/-- Fact 1, p. 28: an edge agent announces `1` at time one iff one of its two vertex agents
has signal `1`. -/
theorem fact_1 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k₀ k₁ : ℝ)
    (s : Agent n G → Bool) (e : G.edgeSet) :
    act (vcNet G k₀ k₁) 1 (Agent.edg e) s = true ↔
      ∃ v ∈ (e : Sym2 (Fin n)), s (Agent.vtx v) = true := by sorry

end BayesGroupHard.VertexCover
