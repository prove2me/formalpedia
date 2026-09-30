-- Prove2me | Theorems.Thm_ChenWhitt93_JumpDiffusion_lemma_4_2
-- name    : ChenWhitt93.JumpDiffusion.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:51:22.546427+00:00
-- url     : https://prove2.me/theorems/5cce5052-849f-4ea4-9254-cf3b4fc741cb
-- title:
--   Lemma 4.2 — fluid limit of the busy time, $n^{-1}B^n_j(nt)\to t$ u.o.c. (printed $n^{-1/2}$ corrected)
-- statement:
--   Consider a sequence of networks with a common routing, a limit $(\hat Z(0),\hat A,\hat S,\hat R,(u^j_k,d^j_k))$, and parameters $\lambda^n,\mu^n,\lambda,\mu,c_\lambda,c_\mu,P$, all deterministic. Assume the hypotheses of the almost-sure part of the proof of Theorem 4.1:
--
--   1. every network satisfies the standing assumptions of Section 3;
--   2. (4.6)–(4.8);
--   3. (4.18)–(4.22): $n^{-1/2}Z^n(0)\to\hat Z(0)$, $n^{-1/2}[A^n(nt)-\lambda^nnt]\to\hat A(t)$, $n^{-1/2}[S^n(nt)-\mu^nnt]\to\hat S(t)$ and $n^{-1/2}[R_{kj}(\lfloor nt\rfloor)-P_{kj}nt]\to\hat R_{kj}(t)$ u.o.c., and $(u^{j,n}_k/n,d^{j,n}_k/\sqrt n)\to(u^j_k,d^j_k)$ for every $j,k$;
--   4. $\hat A,\hat S,\hat R$ are continuous, $\sum_k u^j_k=\infty$, and (4.11) holds.
--
--   Let $(Z^n,B^n)$ solve the network equations (3.2)–(3.3) of network $n$. Then for every station $j$
--   $$
--   \frac1n B^n_j(nt)\to t\qquad\text{u.o.c. as }n\to\infty.
--   $$
--
--   The lemma says that, at the fluid scale, every station is busy almost all of the time: the network is asymptotically balanced, and the down times are negligible at this scale. It is what allows the random time change $S_k(B_k(\cdot))$ in (4.23) to be replaced by the identity, giving (4.24).
--
--   **Formalization Note** The page prints $\frac1{\sqrt n}B^n_j(nt)\to t$. That is false: $B^n_j(nt)\le nt$, and under the assumptions it is of order $nt$, so $n^{-1/2}B^n_j(nt)$ diverges for $t>0$. The proof ((4.33)–(4.40), pp. 353–354) is about $n^{-1}B^n(nt)$ throughout, so the corrected scaling $n^{-1}$ is stated.
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), p. 351, Lemma 4.2 (printed with 1/√n; the proof on pp. 353–354, (4.33)–(4.40), uses 1/n), under the assumptions (4.6)–(4.8), (4.18)–(4.22) of p. 351

import Mathlib
import Definitions.Def_ChenWhitt93_JumpDiffusion_HeavyTraffic

namespace ChenWhitt93.JumpDiffusion

open Filter Topology MeasureTheory Matrix

/-- Lemma 4.2 (p. 351), with the scaling of its proof ((4.33)–(4.40)): under the pathwise
assumptions of the proof of Theorem 4.1, `n⁻¹ Bⱼⁿ(nt) → t` u.o.c. for every station `j`.
(The page prints `n^{-1/2}` in place of `n⁻¹`.) -/
theorem lemma_4_2 {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (net : ℕ → NetworkData J)
    (lamn mun : ℕ → Fin J → ℝ) (lam mu clam cmu : Fin J → ℝ) (P : Matrix (Fin J) (Fin J) ℝ)
    (L : LimitData J) (Z : ℕ → ℝ → Fin J → ℤ) (B : ℕ → ℝ → Fin J → ℝ)
    (hH : PathwiseHyp χ net lamn mun lam mu clam cmu P L)
    (hsol : ∀ n, IsQueueSolution χ (net n) (Z n) (B n)) :
    ∀ j : Fin J, UocTendsto (fun (n : ℕ) (t : ℝ) => B n (n * t) j / n) (fun t => t) := by sorry

end ChenWhitt93.JumpDiffusion
