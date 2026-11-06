-- Prove2me | Theorems.Thm_DelayedGamesMAO_fact_1
-- name    : DelayedGamesMAO.fact_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:27:52.196881+00:00
-- url     : https://prove2.me/theorems/47257f83-ef85-4d18-8b59-0efb5f0e6a41
-- title:
--   Fact 1 — delay-set identities and $q_{\max}^2\le T+2d_{\mathrm{tot}}$
-- statement:
--   Let $T\ge1$ and let $(d_t)$ be delays with $t+d_t\le T$ for every $t\in[T]$ (every feedback arrives within the horizon). Then:
--
--   1. for every $t\in[T]$: $O_t\sqcup P_t=[t-1]$, $O_{t+1}=O_t\sqcup N_t$ and $A_t=P_{t+1}\sqcup N_t$;
--   2. $N_1,\dots,N_T$ partition $[T]$;
--   3. for every $t\in[T]$, $q_{t+1}=q_t+1-|N_t|\le q_t+1$; moreover $q_1=1$ and $P_1=P_{T+1}=\varnothing$;
--   4. $\sum_{t\in[T]}\sigma_t=d_{\mathrm{tot}}$;
--   5. $$q_{\max}^2\le T+2d_{\mathrm{tot}}.$$
--
--   These identities are the bookkeeping behind every delay argument of the paper; item 5 converts the self-play rate $O(q_{\max})$ into the adversarial rate $O(\sqrt{T+d_{\mathrm{tot}}})$.
--
--   **Formalization Note** Each disjoint union $\sqcup$ is a union together with pairwise disjointness; the partition in item 2 is pairwise disjointness of the $N_t$ together with $\bigcup_{t\in[T]}N_t=[T]$. The identity in item 3 is stated in the integers.
--
--   Differences from the source:
--   - encoding: the protocol's standing assumption that g_t is revealed at the end of round t + d_t ≤ T (p.3, footnote 1) → hypothesis ∀ t ∈ [T], t + d t ≤ T; reason: part of the model stated once in §2; no instance of the paper is excluded
--   - encoding: A ⊔ B (disjoint union); N_1, …, N_T partition [T] → A ∪ B together with Disjoint A B; pairwise disjoint N_t with union [T]; reason: the meaning of the notation; same instances
--   - encoding: q_{t+1} = q_t + 1 − |N_t| → the same identity cast to ℤ; reason: avoids truncated natural subtraction; same instances
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), Appendix D, Fact 1, p.38

import Mathlib
import Definitions.Def_DelayedGamesMAO_observed
import Definitions.Def_DelayedGamesMAO_newObs
import Definitions.Def_DelayedGamesMAO_q
import Definitions.Def_DelayedGamesMAO_sigma
import Definitions.Def_DelayedGamesMAO_qmax
import Definitions.Def_DelayedGamesMAO_dtot

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Fact 1 (delay-set identities).**
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), Appendix D, Fact 1, p.38: "The following properties hold for every `t ∈ [T]`:
(a) `O_t ⊔ P_t = [t − 1]`, `O_{t+1} = O_t ⊔ N_t`, `A_t = P_{t+1} ⊔ N_t`; (b) `N_1, …, N_T`
partition `[T]`; (c) `q_{t+1} = q_t + 1 − |N_t| ≤ q_t + 1`, `q_1 = 1`, `P_1 = P_{T+1} = ∅`;
(d) `∑_{t∈[T]} σ_t = d_tot` under the assumption that `t + d_t ≤ T` for every `t`;
(e) `q_max² ≤ T + 2d_tot`."

**Formalization Note.** `T ∈ ℕ₊` is `1 ≤ T`. The hypothesis `t + d_t ≤ T` for `t ∈ [T]` is
the protocol's (p.3: "`g_t` is revealed at the end of round `t + d_t ≤ T`"). Each `⊔` is a
union together with disjointness. (c)'s identity is stated in `ℤ` to avoid truncated
subtraction. -/
theorem fact_1 (T : ℕ) (hT : 1 ≤ T) (d : ℕ → ℕ) (hd : ∀ t ∈ Finset.Icc 1 T, t + d t ≤ T) :
    (∀ t ∈ Finset.Icc 1 T,
      (Disjoint (observed d t) (pending d t) ∧
        observed d t ∪ pending d t = Finset.Icc 1 (t - 1)) ∧
      (Disjoint (observed d t) (newObs d t) ∧
        observed d (t + 1) = observed d t ∪ newObs d t) ∧
      (Disjoint (pending d (t + 1)) (newObs d t) ∧
        active d t = pending d (t + 1) ∪ newObs d t)) ∧
    ((∀ t ∈ Finset.Icc 1 T, ∀ t' ∈ Finset.Icc 1 T, t ≠ t' →
        Disjoint (newObs d t) (newObs d t')) ∧
      (Finset.Icc 1 T).biUnion (newObs d) = Finset.Icc 1 T) ∧
    ((∀ t ∈ Finset.Icc 1 T,
        (q d (t + 1) : ℤ) = q d t + 1 - (newObs d t).card ∧ q d (t + 1) ≤ q d t + 1) ∧
      q d 1 = 1 ∧ pending d 1 = ∅ ∧ pending d (T + 1) = ∅) ∧
    ∑ t ∈ Finset.Icc 1 T, sigma d t = dtot d T ∧
    qmax d T ^ 2 ≤ T + 2 * dtot d T := by sorry

end DelayedGamesMAO
