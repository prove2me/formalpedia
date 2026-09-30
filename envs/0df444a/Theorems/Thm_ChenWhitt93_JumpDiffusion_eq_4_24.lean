-- Prove2me | Theorems.Thm_ChenWhitt93_JumpDiffusion_eq_4_24
-- name    : ChenWhitt93.JumpDiffusion.eq_4_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:52:41.798364+00:00
-- url     : https://prove2.me/theorems/43512750-192e-4875-bb34-85a352c3c560
-- title:
--   Eq. (4.24) — $n^{-1/2}\xi^n(nt)\to\hat\xi(t)$ u.o.c., and $\hat\xi$ is continuous
-- statement:
--   Assume the deterministic hypotheses of the proof of Theorem 4.1, as in Lemma 4.2: Section 3's assumptions on every network, (4.6)–(4.8), (4.18)–(4.22), continuity of $\hat A,\hat S,\hat R$, $\sum_ku^j_k=\infty$, and (4.11). Let $(Z^n,B^n)$ solve (3.2)–(3.3) for network $n$. Let $\xi^n$ be the centred process (3.9) of network $n$, with rates $\lambda^n,\mu^n$ and routing matrix $P$. Then
--   $$
--   \frac1{\sqrt n}\,\xi^n_j(nt)\to\hat\xi_j(t)\qquad\text{u.o.c. as }n\to\infty,\ j=1,\dots,J,
--   $$
--   where
--   $$
--   \hat\xi_j(t)=\hat A_j(t)+\sum_{k=1}^J\big[\hat R_{kj}(\mu_kt)+P_{kj}\hat S_k(t)\big]-\hat S_j(t) \qquad (4.15)
--   $$
--   and $\hat\xi$ is continuous on $[0,\infty)$.
--
--   This is the continuous (Brownian, in typical applications) part of the limit free process. It combines the functional central limit theorems (4.19)–(4.21) with the random time change supplied by Lemma 4.2.
--
--   **Formalization Note** "u.o.c." means uniform convergence on $[0,T]$ for every $T$. The time argument of $\hat R_{kj}$ is $\mu_kt$ with the limit rate $\mu_k$.
-- source:
--   Chen and Whitt, Diffusion approximations for open queueing networks with service interruptions, Queueing Systems 13 (1993), p. 352, Eq. (4.24) (with (3.9), p. 345, and (4.15), p. 350)

import Mathlib
import Definitions.Def_ChenWhitt93_JumpDiffusion_HeavyTraffic

namespace ChenWhitt93.JumpDiffusion

open Filter Topology MeasureTheory Matrix

/-- Eq. (4.24) (p. 352): under the pathwise assumptions of the proof of Theorem 4.1,
`n^{-1/2} ξⁿ(nt) → ξ̂(t)` u.o.c., with `ξⁿ` of (3.9) for network `n` (rates `λⁿ, μⁿ`) and
`ξ̂` of (4.15); moreover `ξ̂` is continuous on `[0, ∞)`. -/
theorem eq_4_24 {J : ℕ} (χ : Fin J → Fin J → ℕ → Bool) (net : ℕ → NetworkData J)
    (lamn mun : ℕ → Fin J → ℝ) (lam mu clam cmu : Fin J → ℝ) (P : Matrix (Fin J) (Fin J) ℝ)
    (L : LimitData J) (Z : ℕ → ℝ → Fin J → ℤ) (B : ℕ → ℝ → Fin J → ℝ)
    (hH : PathwiseHyp χ net lamn mun lam mu clam cmu P L)
    (hsol : ∀ n, IsQueueSolution χ (net n) (Z n) (B n)) :
    UocTendsto (fun (n : ℕ) (t : ℝ) => (Real.sqrt n)⁻¹ • xi χ (net n) (lamn n) (mun n) P (B n) (n * t))
      (xiHat L mu P) ∧
    ContinuousOn (xiHat L mu P) (Set.Ici 0) := by sorry

end ChenWhitt93.JumpDiffusion
