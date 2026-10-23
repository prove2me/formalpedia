-- Prove2me | Theorems.Thm_BayesGroupHard_VertexCover_fact_2
-- name    : BayesGroupHard.VertexCover.fact_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:31.826995+00:00
-- url     : https://prove2.me/theorems/1badc2e1-81fa-4503-8ad1-05b337d4d4a6
-- title:
--   Fact 2, p. 28 — the vertex signals form a vertex cover iff every edge agent announces 1 at time one
-- statement:
--   In the vertex-cover network of a graph $G$ (for any parameters $k_0,k_1$), let $\Sigma = \{v : s_{\tau_v} = 1\}$ be the set of vertices whose vertex agent has signal $1$. Then
--   $$\Sigma \text{ is a vertex cover of } G \iff a_{\varepsilon,1} = 1 \text{ for every edge agent } \varepsilon.$$
--
--   It translates the observation history of agent $i$ into a statement about vertex covers.
--
--   **Formalization Note.** Vertex covers are Mathlib's `SimpleGraph.IsVertexCover`: every edge has an endpoint in the set.
-- source:
--   Hązła, Jadbabaie, Mossel & Rahimian, Bayesian Decision Making in Groups is Hard, arXiv:1705.04770v4, p. 28, Fact 2

import Mathlib
import Definitions.Def_BayesGroupHard_VertexCover_Model

open Finset

namespace BayesGroupHard.VertexCover

/-- Fact 2, p. 28: the set `Σ = {v : s_{τ_v} = 1}` is a vertex cover iff every edge agent
announces `1` at time one. -/
theorem fact_2 {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k₀ k₁ : ℝ)
    (s : Agent n G → Bool) :
    G.IsVertexCover {v | s (Agent.vtx v) = true} ↔
      ∀ e : G.edgeSet, act (vcNet G k₀ k₁) 1 (Agent.edg e) s = true := by sorry

end BayesGroupHard.VertexCover
