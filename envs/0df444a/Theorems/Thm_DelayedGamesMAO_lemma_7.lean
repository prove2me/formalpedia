-- Prove2me | Theorems.Thm_DelayedGamesMAO_lemma_7
-- name    : DelayedGamesMAO.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:24:46.560317+00:00
-- url     : https://prove2.me/theorems/963f8d45-962a-48e4-a40c-78f171362fd6
-- title:
--   Lemma 7 — re-indexing sums by arrival time
-- statement:
--   Let $T\ge1$ and let $(d_t)$ be delays with $t+d_t\le T$ for $t\in[T]$. For all nonnegative reals $(\delta_t)_t$ and $(\lambda^{(t)}_s)_{s,t}$,
--   $$
--   \sum_{t=1}^T\sum_{s\in N_t}\lambda^{(t+1)}_s\delta_s=\sum_{t=1}^T\lambda^{(t+d_t+1)}_t\delta_t .
--   $$
--
--   Summing over arrival times instead of rounds converts the prediction-error terms of the update into per-round terms.
--
--   Differences from the source:
--   - encoding: the protocol's standing assumption that g_t is revealed at the end of round t + d_t ≤ T (p.3, footnote 1) → hypothesis ∀ t ∈ [T], t + d t ≤ T; reason: part of the model stated once in §2; no instance of the paper is excluded
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), Appendix D, Lemma 7, p.39

import Mathlib
import Definitions.Def_DelayedGamesMAO_newObs

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Lemma 7 (re-indexing by arrival time).**
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), Appendix D, Lemma 7, p.39: "Let `(δ_t)_t` and `(λ_s^{(t)})_{s,t}` be arbitrary non-negative
sequences of real numbers. Then `∑_{t=1}^T ∑_{s∈N_t} λ_s^{(t+1)} δ_s = ∑_{t=1}^T λ_t^{(t+d_t+1)} δ_t`."

`lam t s` is `λ_s^{(t)}` (superscript first).

**Formalization Note.** The protocol's `t + d_t ≤ T` (every feedback arrives within the horizon)
is a hypothesis. -/
theorem lemma_7 (T : ℕ) (hT : 1 ≤ T) (d : ℕ → ℕ) (hd : ∀ t ∈ Finset.Icc 1 T, t + d t ≤ T)
    (δ : ℕ → ℝ) (lam : ℕ → ℕ → ℝ) (hδ : ∀ t, 0 ≤ δ t) (hlam : ∀ t s, 0 ≤ lam t s) :
    ∑ t ∈ Finset.Icc 1 T, ∑ s ∈ newObs d t, lam (t + 1) s * δ s =
      ∑ t ∈ Finset.Icc 1 T, lam (t + d t + 1) t * δ t := by sorry

end DelayedGamesMAO
