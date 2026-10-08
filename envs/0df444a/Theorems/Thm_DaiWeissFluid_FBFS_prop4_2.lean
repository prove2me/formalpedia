-- Prove2me | Theorems.Thm_DaiWeissFluid_FBFS_prop4_2
-- name    : DaiWeissFluid.FBFS.prop4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:38:26.786536+00:00
-- url     : https://prove2.me/theorems/ab4db39d-aa2a-4820-8bd4-9597b6b81486
-- title:
--   Proposition 4.2 — flow rates of a preemptive-resume priority fluid model
-- statement:
--   Consider a reentrant line with mean service times $m_k > 0$, a buffer priority ranking $\pi$, and a solution $(Q,T)$ of the priority fluid model (1.8)–(1.12), (4.4). Let $t > 0$ be a regular time, at which every $T_k$ has derivative $\dot T_k(t)$, and let $a_k = \mu_{k-1}\dot T_{k-1}(t)$ and $d_k = \mu_k\dot T_k(t)$ be the in-flow and out-flow rates (4.5).
--
--   1. (a) $a_k = d_{k-1}$ for every $k$, with $d_0 = 1$.
--   2. (b) If $Q_k(t) = 0$, then $a_k = d_k$.
--   3. (c) If $k_0$ is the highest-priority nonempty class at station $\sigma(k_0)$, i.e. $Q_{k_0}(t) > 0$ and $Q_l(t) = 0$ for every class $l$ at that station with $\pi(l) < \pi(k_0)$, then
--   $$
--   \sum_{k\in H_{k_0}} m_k d_k = 1, \tag{4.6}
--   $$
--   and every class $l$ at the same station with lower priority, $\pi(l) > \pi(k_0)$, has $d_l = 0$. In particular at most one nonempty buffer at a station, the highest-priority one, can have a positive out-flow rate.
--
--   These rate identities are the local description of a priority fluid model; the stability proofs for FBFS (Theorem 4.3) and LBFS (Theorem 4.4) are built from them.
--
--   **Formalization Note** The regular point is encoded by derivatives `dT k` with `HasDerivAt (fun s => T s k) (dT k) t` for all $k$ (the paper's "regular point for $Q$, $T$ and $B$"; $Q$ and $B$ are then differentiable by (1.8) and (1.11)). Part (a) holds by the definition of `inRate`, and is not repeated in the conclusion; the sentence "at most one non-empty buffer … can have positive out-flow rate" follows from the last clause of (c), which is stated. Classes are 0-based. Positivity $m_k > 0$ is stated explicitly. Condition (1.7) is not needed.
-- source:
--   Dai and Weiss, Stability and instability of fluid models for reentrant lines, Math. Oper. Res. 21(1) (1996), p. 123, Proposition 4.2, (4.5)–(4.6)

import Mathlib
import Definitions.Def_DaiWeissFluid_FBFS_FluidModel

namespace DaiWeissFluid.FBFS

/-- Proposition 4.2, p. 123, for an arbitrary preemptive-resume priority ranking `π`. At a regular
time `t > 0` (every `T_k` differentiable at `t`, with derivative `dT k`), with the rates
`a_k = inRate`, `d_k = outRate` of (4.5): (b) an empty buffer has equal in- and out-flow rates;
(c) if `k₀` is non-empty and every class of higher priority at its station is empty, then
`∑_{k ∈ H_{k₀}} m_k d_k = 1` (4.6), and every class of lower priority at that station has
out-flow rate `0`. Part (a), `a_k = d_{k-1}` with `d₀ = 1`, is the definition of `inRate`. -/
theorem prop4_2 {I K : ℕ} (L : ReentrantLine I K) (hm : ∀ k, 0 < L.m k)
    (π : Equiv.Perm (Fin K)) (Q T : ℝ → Fin K → ℝ) (hsol : L.IsPrioritySolution π Q T)
    (t : ℝ) (ht : 0 < t) (dT : Fin K → ℝ)
    (hdT : ∀ k, HasDerivAt (fun s => T s k) (dT k) t) :
    (∀ k, Q t k = 0 → L.inRate dT k = L.outRate dT k) ∧
    (∀ k₀, 0 < Q t k₀ → (∀ l, L.σ l = L.σ k₀ → π l < π k₀ → Q t l = 0) →
      (∑ k ∈ L.H π k₀, L.m k * L.outRate dT k = 1) ∧
        ∀ l, L.σ l = L.σ k₀ → π k₀ < π l → L.outRate dT l = 0) := by sorry

end DaiWeissFluid.FBFS
