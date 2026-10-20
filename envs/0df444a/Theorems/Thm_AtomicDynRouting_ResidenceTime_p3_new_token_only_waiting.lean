-- Prove2me | Theorems.Thm_AtomicDynRouting_ResidenceTime_p3_new_token_only_waiting
-- name    : AtomicDynRouting.ResidenceTime.p3_new_token_only_waiting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:07.808831+00:00
-- url     : https://prove2.me/theorems/39c1cdee-a565-4796-bbdd-e28c41df9fd1
-- title:
--   (p3), p. 9 — at s > r0, ζ produces a new token only if he stays in the same buffer during [s − 1, s]
-- statement:
--   Let $G$ be a finite acyclic network with unit lengths and capacities, take an ADR run, a focal agent $\zeta$ with entry time $r$, and an integer time $r_0\ge r$, and consider the token process of §3.2 started at $r_0$.
--
--   If at an integer time $s>r_0$ agent $\zeta$ produces a new token, i.e. the number of tokens produced by time $s$ exceeds the number produced by time $s-1$, then $\zeta$ is in the buffer of the same edge of his route at both times $s-1$ and $s$.
--
--   This is observation (p3) of the paper: a new token is produced only while $\zeta$ waits.
-- source:
--   Cao, Chen, Chen, Wang, Bounding residence times for atomic dynamic routings, accepted manuscript (Mathematics of Operations Research, accepted Nov. 12, 2021; WRAP 160244), p. 9 (PDF 10), §3.2, (p3)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Tokens

namespace AtomicDynRouting.ResidenceTime

/-- (p3), §3.2, p. 9. At any time `s > r0`, agent `ζ` produces a new token only if he stays in the same buffer during `[s − 1, s]`. -/
theorem p3_new_token_only_waiting {V E ι : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (N : Network V E) (hN : N.Acyclic) (R : RunData ι E V) (hR : IsADR N R) (ζ : ι) (r0 : ℕ) (hr0 : R.entry ζ ≤ r0) (hinside : R.inside ζ r0) (s : ℕ) (hs : r0 < s) (hnew : produced R ζ r0 (s - 1) < produced R ζ r0 s) : ∃ j : ℕ, R.inBuf ζ j (s - 1) ∧ R.inBuf ζ j s := by sorry

end AtomicDynRouting.ResidenceTime
