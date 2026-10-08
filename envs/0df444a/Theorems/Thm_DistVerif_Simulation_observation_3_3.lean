-- Prove2me | Theorems.Thm_DistVerif_Simulation_observation_3_3
-- name    : DistVerif.Simulation.observation_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:24:03.967303+00:00
-- url     : https://prove2.me/theorems/064a50c7-ecc4-4c17-8de6-367cd0c4d560
-- title:
--   Observation 3.3 — $C_{\mathcal A}(U,t,x,y)$ is determined by $C_{\mathcal A}(U',t-1,x,y)$ and the messages into $U$ from $V\setminus U'$
-- statement:
--   Let $G$ be any graph on a vertex set $V$ with designated input vertices $s,r$, and let $\mathcal A$ be a deterministic B-model algorithm on it. For $U\subseteq V$ write $C_{\mathcal A}(U,t,x,y)$ for the configuration of $U$ at the end of round $t$ of the execution on inputs $(x,y)$, i.e. the vector of states $\sigma_{\mathcal A}(v,t,x,y)$, $v\in U$.
--
--   Let $U\subseteq U'\subseteq V$, $t\in\mathbb N$, and let $(x,y)$, $(x',y')$ be two input pairs. Suppose that
--
--   1. $C_{\mathcal A}(U',t,x,y)=C_{\mathcal A}(U',t,x',y')$, and
--   2. for every edge $(w,u)$ with $w\in V\setminus U'$ and $u\in U$, the message $w$ sends to $u$ in round $t+1$ is the same in both executions.
--
--   Then
--   $$C_{\mathcal A}(U,t+1,x,y)=C_{\mathcal A}(U,t+1,x',y').$$
--
--   This is the paper's statement that $C_{\mathcal A}(U,t,x,y)$ "can be uniquely determined by" $C_{\mathcal A}(U',t-1,x,y)$ and all messages sent to $U$ from $V\setminus U'$ at time $t$, with the round index shifted by one. It is the locality principle behind Lemma 3.4: knowledge propagates along edges one hop per round.
--
--   **Formalization Note** "Uniquely determined by" is stated as agreement of two executions, which is equivalent to the existence of a function, independent of the inputs, mapping the data to the configuration. The round pair $(t-1,t)$ of the paper is $(t,t+1)$ here, avoiding natural-number subtraction.
-- source:
--   Das Sarma, Holzer, Kor, Korman, Nanongkai, Pandurangan, Peleg, Wattenhofer, Distributed Verification and Hardness of Distributed Approximation, SIAM J. Comput. 41 (2012), p. 1249, Observation 3.3

import Mathlib
import Definitions.Def_DistVerif_Simulation_Algorithm

namespace DistVerif.Simulation

/-- **Observation 3.3** (p. 1249). For `U ⊆ U' ⊆ V`, the configuration of `U` at the end of
round `t + 1` is determined by the configuration of `U'` at the end of round `t` and the
messages sent to `U` from `V \ U'` in round `t + 1`: two executions (on inputs `(x, y)` and
`(x', y')`) that agree on both agree on the states of `U` after round `t + 1`. -/
theorem observation_3_3 {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (s r : V) {B b : ℕ} (A : DetAlg V B b) (U U' : Set V) (hUU' : U ⊆ U')
    (x y x' y' : Fin b → Bool) (t : ℕ)
    (hconf : ∀ v ∈ U', A.exec G s r x y t v = A.exec G s r x' y' t v)
    (hmsg : ∀ w u : V, w ∉ U' → u ∈ U → G.Adj w u →
      A.send w u (A.exec G s r x y t w) = A.send w u (A.exec G s r x' y' t w)) :
    ∀ v ∈ U, A.exec G s r x y (t + 1) v = A.exec G s r x' y' (t + 1) v := by sorry

end DistVerif.Simulation
