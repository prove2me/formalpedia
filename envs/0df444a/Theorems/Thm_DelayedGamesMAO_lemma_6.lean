-- Prove2me | Theorems.Thm_DelayedGamesMAO_lemma_6
-- name    : DelayedGamesMAO.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:29:12.569259+00:00
-- url     : https://prove2.me/theorems/68c2553d-9f96-4b4b-9968-152855eba599
-- title:
--   Lemma 6 — the congestion schedule (10) is an allocation schedule
-- statement:
--   Let $T\ge1$ and $(d_t)$ delays with $t+d_t\le T$. The array $\alpha^{(t)}_s=\mathbb 1\{s\in A_t\}/\kappa_{s,t}$, $1\le s\le t\le T+1$, of (10) is an allocation schedule in the sense of Definition 1.
--
--   This lets Theorem 5 apply to the schedule used by MAO-OMD.
--
--   Differences from the source:
--   - encoding: (10) printed for 1 ≤ s ≤ t ≤ T, used up to T + 1 → the same formula for every t, including T + 1; reason: it gives α^{(T+1)}_s = 0 for s ≤ T, as Definition 1 requires
--   - encoding: the protocol's standing assumption that g_t is revealed at the end of round t + d_t ≤ T (p.3, footnote 1) → hypothesis ∀ t ∈ [T], t + d t ≤ T; reason: part of the model stated once in §2; no instance of the paper is excluded
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §6.4, Lemma 6, p.22

import Mathlib
import Definitions.Def_DelayedGamesMAO_IsAllocationSchedule
import Definitions.Def_DelayedGamesMAO_congAlloc

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Lemma 6 (the congestion schedule (10) is an allocation schedule).**
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §6.4, Lemma 6, p.22: "The sequence `(α_s^{(t)})_{1≤s≤t≤T+1}` from Equation (10) is an
allocation schedule in the sense of Definition 1."

**Formalization Note.** (10) is `congAlloc d`, extended to `t = T + 1` by the same formula. The
protocol's `t + d_t ≤ T` is a hypothesis. -/
theorem lemma_6 (T : ℕ) (hT : 1 ≤ T) (d : ℕ → ℕ) (hd : ∀ t ∈ Finset.Icc 1 T, t + d t ≤ T) :
    IsAllocationSchedule d T (congAlloc d) := by sorry

end DelayedGamesMAO
