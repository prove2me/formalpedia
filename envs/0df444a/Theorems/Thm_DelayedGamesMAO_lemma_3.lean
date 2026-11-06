-- Prove2me | Theorems.Thm_DelayedGamesMAO_lemma_3
-- name    : DelayedGamesMAO.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:27:48.73136+00:00
-- url     : https://prove2.me/theorems/4c29eabe-d0e5-48e8-87bc-5881774c7d2b
-- title:
--   Lemma 3 — at most $\sigma_{\max}$ later rounds have no hint source
-- statement:
--   Let $T\ge1$ and $(d_t)$ delays with $t+d_t\le T$. Let $s_1,\dots,s_{T+1}$ be any choice such that, for every $t\in[T+1]$, with $S_t=\{s_1,\dots,s_{t-1}\}$: $s_t\in O_t\setminus S_t$ whenever $O_t\setminus S_t\ne\varnothing$, and $s_t=0$ otherwise. Then
--   $$
--   |\{t\in[T]: s_{t+1}=0\}|\le\sigma_{\max}\qquad\text{and}\qquad|\{t\in[T]: s_t=0\}|\le q_{\max}.
--   $$
--
--   The reference point $w_0$ serves as a hint source at most $q_{\max}$ times; every other observed round serves at most once.
--
--   **Formalization Note** The choice is any sequence of naturals; only its terms $s_1,\dots,s_{T+1}$ are constrained.
--
--   Differences from the source:
--   - encoding: the protocol's standing assumption that g_t is revealed at the end of round t + d_t ≤ T (p.3, footnote 1) → hypothesis ∀ t ∈ [T], t + d t ≤ T; reason: part of the model stated once in §2; no instance of the paper is excluded
--   - encoding: rounds 1, …, T (and T + 1) and finite sequences indexed by them → natural numbers and sequences ℕ → … whose terms outside the used indices are unconstrained; reason: only the paper's indices are read; same instances
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §6.3, Lemma 3, p.18

import Mathlib
import Definitions.Def_DelayedGamesMAO_observed
import Definitions.Def_DelayedGamesMAO_sigmaMax
import Definitions.Def_DelayedGamesMAO_qmax

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Lemma 3 (at most `σ_max` later rounds, and `q_max` rounds in all, have no hint source).**
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §6.3, Lemma 3, p.18: "Consider any choice of `s_1, …, s_{T+1}` such that, for every
`t ∈ [T + 1]`, `s_t ∈ O_t \ S_t` whenever `O_t \ S_t ≠ ∅` and `s_t = 0` otherwise, where
`S_t := {s_1, …, s_{t−1}}`. Then, `|{t ∈ [T] : s_{t+1} = 0}| ≤ σ_max` and
`|{t ∈ [T] : s_t = 0}| ≤ q_max`."

**Formalization Note.** `s : ℕ → ℕ` is any sequence; only `s_1, …, s_{T+1}` are constrained, and
`S_t` is the image of `[t − 1]` under `s`. The protocol's `t + d_t ≤ T` is a hypothesis. -/
theorem lemma_3 (T : ℕ) (hT : 1 ≤ T) (d : ℕ → ℕ) (hd : ∀ t ∈ Finset.Icc 1 T, t + d t ≤ T)
    (s : ℕ → ℕ)
    (hs : ∀ t ∈ Finset.Icc 1 (T + 1),
      (observed d t \ (Finset.Icc 1 (t - 1)).image s).Nonempty →
        s t ∈ observed d t \ (Finset.Icc 1 (t - 1)).image s)
    (hs0 : ∀ t ∈ Finset.Icc 1 (T + 1),
      observed d t \ (Finset.Icc 1 (t - 1)).image s = ∅ → s t = 0) :
    ((Finset.Icc 1 T).filter (fun t => s (t + 1) = 0)).card ≤ sigmaMax d T ∧
      ((Finset.Icc 1 T).filter (fun t => s t = 0)).card ≤ qmax d T := by sorry

end DelayedGamesMAO
