-- Prove2me | Theorems.Thm_ForkJoinCtrl_Tracking_lemma_5
-- name    : ForkJoinCtrl.Tracking.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:17:30.851007+00:00
-- url     : https://prove2.me/theorems/10173189-d6a3-4d4e-8cc0-cdef9c573bf9
-- title:
--   Lemma 5, p. 22 — exponential tail bounds (43a)–(43c) for arrival and service processes over [τ^r_ln, τ^r_ln + ar]
-- statement:
--   Assume Assumptions 1–2 and consider runs of the proposed policy for every $r$. Fix $T>0$ and $a,b>0$. There are $r_1\in\mathbb N_+$ and $C_9,C_{10}>0$ such that for all $r\ge r_1$, $j\in\mathcal J$, $i\in\mathcal I_j$, $k\in\mathcal K_j$, $l\in\mathcal I$ and $n\in\{1,\dots,M^r\}$:
--
--   $$\mathbf P\Big(\sup_{0\le t\le ar}|A^r_j(\tau^r_{ln}+t)-A^r_j(\tau^r_{ln})-\lambda^r_jt|>br,\ \tau^r_{ln}\le r^2T,\ B^r\Big)\le C_9r^2e^{-C_{10}r},\tag{43a}$$
--
--   and the same bound holds for $S_{ij}(T^r_{ij}(\tau^r_{ln})+t)-S_{ij}(T^r_{ij}(\tau^r_{ln}))-\mu_{ij}t$ (43b) and for $S_k(T^r_k(\tau^r_{ln})+t)-S_k(T^r_k(\tau^r_{ln}))-\mu_kt$ (43c).
--
--   These bounds control the primitives after the random review epochs.
--
--   **Formalization Note** "$\sup_{0\le t\le ar}|\cdot|>br$" is written as "for some $t\in[0,ar]$, $|\cdot|>br$", which is equivalent. $T$, which the paper fixes in Appendix C, is a parameter; $M^r$ and $B^r$ are those of the Bounds definition for this $T$. The constants come after $T,a,b$ (and the runs) and before $r$, $n$ and the indices.
-- source:
--   Özkan, Control of Fork-Join Processing Networks with Multiple Job Types and Parallel Shared Resources, arXiv:2002.01496v1, p. 22, Lemma 5, (43a)–(43c), (42)

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_Bounds

open MeasureTheory Filter Topology

namespace ForkJoinCtrl.Tracking

theorem lemma_5 {N : Network} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (M : Model N Ω P) (hA1 : M.Assumption1) (hA2 : M.Assumption2)
    (run : ∀ r : ℕ, PolicyRun M r) (T : ℝ) (hT : 0 < T) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∃ r1 : ℕ, 1 ≤ r1 ∧ ∃ C9 : ℝ, 0 < C9 ∧ ∃ C10 : ℝ, 0 < C10 ∧ ∀ r : ℕ, r1 ≤ r →
      (∀ (j : Fin N.J) (l : Fin N.I) (n : ℕ), 1 ≤ n → n ≤ N.Mr T r →
        P {ω | (∃ t ∈ Set.Icc 0 (a * r),
              b * r < |(M.A r j ω (((run r).tau l n ω).toReal + t) : ℝ)
                - (M.A r j ω ((run r).tau l n ω).toReal : ℝ) - M.lamr r j * t|) ∧
            (run r).tau l n ω ≤ ENNReal.ofReal ((r : ℝ) ^ 2 * T) ∧ ω ∈ M.Bevent T r}
          ≤ ENNReal.ofReal (C9 * (r : ℝ) ^ 2 * Real.exp (-C10 * r))) ∧
      (∀ (j : Fin N.J) (i : Fin N.I) (l : Fin N.I) (n : ℕ), N.P i j = true → 1 ≤ n →
        n ≤ N.Mr T r →
        P {ω | (∃ t ∈ Set.Icc 0 (a * r),
              b * r < |(M.Ss i j ω ((run r).Tij i j ω ((run r).tau l n ω).toReal + t) : ℝ)
                - (M.Ss i j ω ((run r).Tij i j ω ((run r).tau l n ω).toReal) : ℝ)
                - N.mu i j * t|) ∧
            (run r).tau l n ω ≤ ENNReal.ofReal ((r : ℝ) ^ 2 * T) ∧ ω ∈ M.Bevent T r}
          ≤ ENNReal.ofReal (C9 * (r : ℝ) ^ 2 * Real.exp (-C10 * r))) ∧
      (∀ (k : Fin N.K) (l : Fin N.I) (n : ℕ), 1 ≤ n → n ≤ N.Mr T r →
        P {ω | (∃ t ∈ Set.Icc 0 (a * r),
              b * r < |(M.S k ω ((run r).Tk k ω ((run r).tau l n ω).toReal + t) : ℝ)
                - (M.S k ω ((run r).Tk k ω ((run r).tau l n ω).toReal) : ℝ)
                - N.muK k * t|) ∧
            (run r).tau l n ω ≤ ENNReal.ofReal ((r : ℝ) ^ 2 * T) ∧ ω ∈ M.Bevent T r}
          ≤ ENNReal.ofReal (C9 * (r : ℝ) ^ 2 * Real.exp (-C10 * r))) := by sorry

end ForkJoinCtrl.Tracking
