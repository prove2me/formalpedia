-- Prove2me | Theorems.Thm_AtomicDynRouting_ResidenceTime_token_exit_bound
-- name    : AtomicDynRouting.ResidenceTime.token_exit_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:19:07.900023+00:00
-- url     : https://prove2.me/theorems/1b0d9ca0-137f-4354-99e8-53e577a4cff1
-- title:
--   §3.2, p. 9, sentence above Lemma 1 — each token k exits Gζ no later than r0 + (Loζdζ + k − 1)
-- statement:
--   Let $G$ be a finite acyclic network with unit lengths and capacities, take an ADR run, a focal agent $\zeta$ with entry time $r$, an integer time $r_0\ge r$, and the token process of §3.2 started at $r_0$. Write $L=L_{o_\zeta d_\zeta}$.
--
--   Every token $k\ge1$ that is ever produced exits $G_\zeta$ no later than
--   $$r_0+(L+k-1).$$
--
--   Precisely, there are a time $s$ and an edge $e$ of $G_\zeta$ such that token $k$ is in the buffer of $e$ at time $s$, after the move during $(s,s+1)$ it is no longer in a buffer of $G_\zeta$ (it reaches the sink of $T_k\cap G_\zeta$, exiting $G_\zeta$, at time $s+1$), and $s+1\le r_0+(L+k-1)$.
--
--   The paper derives this from Lemma 1; it is the form used in the proof of Theorem 1.
--
--   **Formalization Note.** The bound is written additively, $s+2\le r_0+L+k$.
-- source:
--   Cao, Chen, Chen, Wang, Bounding residence times for atomic dynamic routings, accepted manuscript (Mathematics of Operations Research, accepted Nov. 12, 2021; WRAP 160244), p. 9 (PDF 10), §3.2, sentence above Lemma 1; used in the proof of Theorem 1, p. 10 (PDF 11)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Tokens

namespace AtomicDynRouting.ResidenceTime

/-- §3.2, p. 9, sentence above Lemma 1. Each token `k` exits `Gζ` no later than `r0 + (L_{oζdζ} + k − 1)`: it leaves the buffer of its last edge `e` of `Gζ` at a time `s` with `s + 1 ≤ r0 + L_{oζdζ} + k − 1`. -/
theorem token_exit_bound {V E ι : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (N : Network V E) (hN : N.Acyclic) (R : RunData ι E V) (hR : IsADR N R) (ζ : ι) (r0 : ℕ) (hr0 : R.entry ζ ≤ r0) (hinside : R.inside ζ r0) (k : ℕ) (hk : 1 ≤ k) (hex : ∃ s : ℕ, tokAt R ζ r0 s k ≠ none) : ∃ (s : ℕ) (e : E), e ∈ Gz N R ζ ∧ tokAt R ζ r0 s k = some e ∧ (∀ e' : E, tokAt R ζ r0 (s + 1) k = some e' → e' ∉ Gz N R ζ) ∧ s + 2 ≤ r0 + N.longest (R.orig ζ) (R.dest ζ) + k := by sorry

end AtomicDynRouting.ResidenceTime
