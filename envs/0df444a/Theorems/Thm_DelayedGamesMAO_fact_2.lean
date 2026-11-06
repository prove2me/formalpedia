-- Prove2me | Theorems.Thm_DelayedGamesMAO_fact_2
-- name    : DelayedGamesMAO.fact_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:28:10.640934+00:00
-- url     : https://prove2.me/theorems/0cef226a-5154-4d48-a13b-f6e888a67b41
-- title:
--   Fact 2 — congestion properties and $\sum_t\kappa_t\le T+2d_{\mathrm{tot}}$
-- statement:
--   Let $T\ge1$ and let $(d_t)$ be delays with $t+d_t\le T$ for every $t\in[T]$. Then:
--
--   1. $\kappa_{t,t}=q_t$ for every $t\in[T]$, and for each round $s\in[T]$ the map $t\mapsto\kappa_{s,t}$ is nondecreasing on $s\le t\le s+d_s$;
--   2. for every $t\in[T]$ and $s\in A_t$: $q_t\le\kappa_{s,t}\le\kappa_s\le q_{\max}$, with $\kappa_{s,t}=\kappa_s$ whenever $s\in N_t$;
--   3. $$\sum_{t=1}^T\kappa_t\le T+2d_{\mathrm{tot}},$$ and consequently, for all $a_1,\dots,a_T\ge0$,
--   $$\sum_{t=1}^T\kappa_ta_t\le\min\Bigl\{q_{\max}\sum_{t=1}^Ta_t,\ (T+2d_{\mathrm{tot}})\max_{t\in[T]}a_t\Bigr\}.$$
--
--   Charging each round by its own congestion instead of $q_{\max}$ is what lets the prediction-error cost of MAO-OMD scale with $T+d_{\mathrm{tot}}$.
--
--   **Formalization Note** The running congestion $\kappa_{s,t}$ is used by the paper on $s\le t\le s+d_s$, and monotonicity is stated on that range.
--
--   Differences from the source:
--   - encoding: the protocol's standing assumption that g_t is revealed at the end of round t + d_t ≤ T (p.3, footnote 1) → hypothesis ∀ t ∈ [T], t + d t ≤ T; reason: part of the model stated once in §2; no instance of the paper is excluded
--   - encoding: t ↦ κ_{s,t} nondecreasing for each fixed s → monotone on s ≤ t ≤ t' ≤ s + d_s for every round s ∈ [T]; reason: κ_{s,t} is defined for s ≤ t ≤ s + d_s (p.4); same content
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), Appendix D, Fact 2, pp.38–39

import Mathlib
import Definitions.Def_DelayedGamesMAO_newObs
import Definitions.Def_DelayedGamesMAO_kappa
import Definitions.Def_DelayedGamesMAO_qmax
import Definitions.Def_DelayedGamesMAO_dtot

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Fact 2 (congestion properties).**
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), Appendix D, Fact 2, pp.38–39: "(a) We have `κ_{t,t} = q_t`, and `t ↦ κ_{s,t}` is
nondecreasing for each fixed `s`. Moreover, `q_t ≤ κ_{s,t} ≤ κ_s ≤ q_max` for every
`s ∈ A_t`, with `κ_{s,t} = κ_s` whenever `s ∈ N_t`. (b) The following bound holds:
`∑_{t=1}^T κ_t ≤ T + 2d_tot`. Consequently, for all `a_1, …, a_T ≥ 0`,
`∑_{t=1}^T κ_t a_t ≤ min{q_max ∑_{t=1}^T a_t, (T + 2d_tot) max_{t∈[T]} a_t}`."

**Formalization Note.** `κ_{s,t}` is `kappaRun d s t` and `κ_s` is `kappa d s`. The running
congestion is defined for `s ≤ t ≤ s + d_s` (p.4), so monotonicity is stated on that range, for
rounds `s ∈ [T]`. The protocol's `t + d_t ≤ T` is a hypothesis. `max_{t∈[T]} a_t` is
`Finset.sup'` over the nonempty `[T]`. -/
theorem fact_2 (T : ℕ) (hT : 1 ≤ T) (d : ℕ → ℕ) (hd : ∀ t ∈ Finset.Icc 1 T, t + d t ≤ T) :
    ((∀ t ∈ Finset.Icc 1 T, kappaRun d t t = q d t) ∧
      (∀ s ∈ Finset.Icc 1 T, ∀ t t' : ℕ, s ≤ t → t ≤ t' → t' ≤ s + d s →
        kappaRun d s t ≤ kappaRun d s t') ∧
      (∀ t ∈ Finset.Icc 1 T, ∀ s ∈ active d t,
        q d t ≤ kappaRun d s t ∧ kappaRun d s t ≤ kappa d s ∧ kappa d s ≤ qmax d T) ∧
      (∀ t ∈ Finset.Icc 1 T, ∀ s ∈ newObs d t, kappaRun d s t = kappa d s)) ∧
    (∑ t ∈ Finset.Icc 1 T, kappa d t ≤ T + 2 * dtot d T ∧
      ∀ a : ℕ → ℝ, (∀ t ∈ Finset.Icc 1 T, 0 ≤ a t) →
        ∑ t ∈ Finset.Icc 1 T, (kappa d t : ℝ) * a t ≤
          min ((qmax d T : ℝ) * ∑ t ∈ Finset.Icc 1 T, a t)
            (((T : ℝ) + 2 * (dtot d T : ℝ)) *
              (Finset.Icc 1 T).sup' (Finset.nonempty_Icc.mpr hT) a)) := by sorry

end DelayedGamesMAO
