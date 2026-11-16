-- Prove2me | Theorems.Thm_BipartiteVRM_Competitive_Supplement_lemma_5_5
-- name    : BipartiteVRM.Competitive.Supplement.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T19:31:15.345191+00:00
-- url     : https://prove2.me/theorems/91e1e51e-4b77-49f0-af12-adc75bffc3f1
-- title:
--   Lemma 5.5 — no negative alternating even cycle at any state of non-bipartite VRM
-- statement:
--   Fix $\gamma>1$, any tie rule and any MPMD input with $|R|=2m$ in any metric space. At every state of non-bipartite VRM, every simple $M^{\mathrm{OFF}}$-alternating even cycle $C$ satisfies
--
--   $$\varphi_{M^{\mathrm{OFF}}}(C)=\gamma D(C\setminus M^{\mathrm{OFF}})-D(C\cap M^{\mathrm{OFF}})\ge0,$$
--
--   where $D$ is the TA distance $D(u,v)=d(x_u,x_v)+|a_u-a_v|$.
--
--   By Lemma 5.3 this makes Steps 1–2 compute genuine minimum augmenting paths throughout the run, so the algorithm is valid.
--
--   Differences from the source:
--   - encoding: a finite request set R with |R| = 2m in any metric space, locations and arrival times a_v ≥ 0 that may coincide → the published MatchingDelays.Linear.Instance n X (labels 0..n−1 in nondecreasing arrival order, any MetricSpace X) with Even n, m = n/2; reason: every finite input can be relabeled in arrival order (simultaneous arrivals in any order); labels give the algorithm no future data, and repeated locations and arrival times are allowed
--   - encoding: an arbitrary but fixed rule for ties among simultaneous events and among the choices of N_uv and v in Steps 1 and 2 → every TieRule, a View-and-history selector over the nonempty finite option sets; reason: the rule sees only received data and its own history; every statement quantifies over all such rules
--   - encoding: every state of non-bipartite VRM → the state after every step index k of the run; reason: the run's states are exactly these; the statement covers all of them
-- source:
--   Tung-Wei Kuo, STOC 2027 submission #528 (October 2026), p. 16, Lemma 5.5

import Definitions.Def_BipartiteVRM_Competitive_Supplement_Specifications

set_option autoImplicit false

namespace BipartiteVRM.Competitive.Supplement

open MatchingDelays.Linear (Instance Edge)

/-- Lemma 5.5, p. 16: every reachable state, every tie rule, every input. -/
theorem lemma_5_5 {n : ℕ} {X : Type*} [MetricSpace X] (I : Instance n X) (hn : Even n)
    (γ : ℝ) (hγ : 1 < γ) (tie : TieRule) (k : ℕ) :
    ∀ C : List ℕ, AlternatingEvenCycle (state I γ tie k).off C →
      0 ≤ netCost (taDist I) γ (state I γ tie k).off (cycleEdges C) := by sorry

end BipartiteVRM.Competitive.Supplement
