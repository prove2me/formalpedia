-- Prove2me | Theorems.Thm_AtomicDynRouting_ResidenceTime_p1_tokens_le_agents
-- name    : AtomicDynRouting.ResidenceTime.p1_tokens_le_agents
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:06.919987+00:00
-- url     : https://prove2.me/theorems/d0a27b2c-e873-4c95-a581-27fa87b0c6a5
-- title:
--   (p1), p. 9 — each agent holds at most one token, and a buffer holds no more tokens than agents
-- statement:
--   Let $G$ be a finite acyclic network with unit lengths and capacities, take an ADR run, a focal agent $\zeta$ with entry time $r$, and an integer time $r_0\ge r$, and consider the token process of §3.2 started at $r_0$.
--
--   Then at every integer time $s\ge r_0$:
--
--   1. each agent holds at most one token during $(s,s+1)$;
--   2. for every edge $e$,
--   $$\#\{\text{tokens in the buffer of } e \text{ at time } s\}\ \le\ \#\{\text{agents in the buffer of } e \text{ at time } s\}.$$
--
--   This is observation (p1) of the paper. It is what lets the proof of Theorem 1 match distinct tokens with distinct agents.
--
--   **Formalization Note.** Both sets in part 2 are finite: token indices are at most the number of tokens produced by time $s$, and the agents in a buffer at time $s$ entered $G$ by time $s$, finitely many per time.
-- source:
--   Cao, Chen, Chen, Wang, Bounding residence times for atomic dynamic routings, accepted manuscript (Mathematics of Operations Research, accepted Nov. 12, 2021; WRAP 160244), p. 9 (PDF 10), §3.2, (p1)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Tokens

namespace AtomicDynRouting.ResidenceTime

/-- (p1), §3.2, p. 9. At any time `s ≥ r0`, each agent holds at most one token, and the number of tokens inside the buffer of an edge `e` is no more than the number of agents in that buffer. -/
theorem p1_tokens_le_agents {V E ι : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (N : Network V E) (hN : N.Acyclic) (R : RunData ι E V) (hR : IsADR N R) (ζ : ι) (r0 : ℕ) (hr0 : R.entry ζ ≤ r0) (hinside : R.inside ζ r0) (s : ℕ) (hs : r0 ≤ s) (a : ι) (e : E) : {k : ℕ | holds R ζ r0 a k s}.Subsingleton ∧ {k : ℕ | tokAt R ζ r0 s k = some e}.ncard ≤ {i : ι | ∃ j, R.inBuf i j s ∧ (R.route i)[j]? = some e}.ncard := by sorry

end AtomicDynRouting.ResidenceTime
