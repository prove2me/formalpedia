-- Prove2me | Theorems.Thm_AtomicDynRouting_ResidenceTime_p2_leaver_holds_token
-- name    : AtomicDynRouting.ResidenceTime.p2_leaver_holds_token
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:09.155928+00:00
-- url     : https://prove2.me/theorems/1b3bd4dd-97cb-4a14-8909-69dda0100213
-- title:
--   (p2), p. 9 — the agent leaving ζ's buffer U_{ζ,s} holds exactly one token; ζ holds a token whenever he moves
-- statement:
--   Let $G$ be a finite acyclic network with unit lengths and capacities, take an ADR run, a focal agent $\zeta$ with entry time $r$, and an integer time $r_0\ge r$, and consider the token process of §3.2 started at $r_0$. Let $s\ge r_0$ be an integer time.
--
--   1. If $U_{\zeta,s}$ is defined ($\zeta$ is inside $G$ at time $s$), then some agent $a$ leaves the buffer $U_{\zeta,s}$ at time $s$, and $a$ holds exactly one token during $(s,s+1)$.
--   2. In particular, if $\zeta$ leaves the buffer of an edge of his route at time $s$, then $\zeta$ holds a token during $(s,s+1)$.
--
--   This is observation (p2) of the paper. Together with (p3) it shows that a new token is only produced while $\zeta$ is being delayed, and that the delaying agent carries a smaller token.
-- source:
--   Cao, Chen, Chen, Wang, Bounding residence times for atomic dynamic routings, accepted manuscript (Mathematics of Operations Research, accepted Nov. 12, 2021; WRAP 160244), p. 9 (PDF 10), §3.2, (p2)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Tokens

namespace AtomicDynRouting.ResidenceTime

/-- (p2), §3.2, p. 9. At any time `s ≥ r0` at which `U_{ζ,s}` is defined, the agent who leaves `U_{ζ,s}` holds exactly one token; in particular `ζ` holds a token whenever he moves. -/
theorem p2_leaver_holds_token {V E ι : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (N : Network V E) (hN : N.Acyclic) (R : RunData ι E V) (hR : IsADR N R) (ζ : ι) (r0 : ℕ) (hr0 : R.entry ζ ≤ r0) (hinside : R.inside ζ r0) (s : ℕ) (hs : r0 ≤ s) : (∀ U : E, zBuf R ζ s = some U → ∃ (a : ι) (j : ℕ), leaver R U s = some (a, j) ∧ ∃! k : ℕ, holds R ζ r0 a k s) ∧ (∀ j : ℕ, j < (R.route ζ).length → R.leave ζ j = (s : ℕ∞) → ∃ k : ℕ, holds R ζ r0 ζ k s) := by sorry

end AtomicDynRouting.ResidenceTime
