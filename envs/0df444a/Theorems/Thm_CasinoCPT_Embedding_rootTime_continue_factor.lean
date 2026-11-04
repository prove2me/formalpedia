-- Prove2me | Theorems.Thm_CasinoCPT_Embedding_rootTime_continue_factor
-- name    : CasinoCPT.Embedding.rootTime_continue_factor
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-03T07:22:54.084867+00:00
-- url     : https://prove2.me/theorems/b5765fa9-668b-40bc-8d32-a3b86e94874a
-- title:
--   p. 47 — P(S_n = x, τ_R ≥ n+1) = P(S_n = x, τ_R ≥ n) · P(ξ_{n,x} = 1) for a randomized Root time
-- statement:
--   Let $S$ be a standard symmetric random walk on a casino space $(\Omega,\mathcal F,P;(\mathcal F_t))$, let $b:\mathbb Z\to\mathbb N$ and $r:\mathbb Z\to\mathbb R$, and let $\{\xi_{t,x}\}$ be $\mathcal F_0$-measurable, mutually independent coins with the laws of (7). Let
--   $$\tau=\tau_R(b,r)=\inf\{t\in\mathbb N:\ t\ge b(S_t),\ \xi_{t,S_t}=0\}$$
--   be the randomized Root stopping time. Then for every $n\in\mathbb N$ and $x\in\mathbb Z$,
--   $$P(S_n=x,\ \tau\ge n+1)=P(S_n=x,\ \tau\ge n)\,P(\xi_{n,x}=1).$$
--
--   This is the factorisation used on p. 47 of the paper in the proof of Proposition A.3, (i) $\Rightarrow$ (ii). On $\{S_n=x,\ \tau\ge n\}$ the walk continues past time $n$ unless $n\ge b(x)$ and $\xi_{n,x}=0$. The event $\{S_n=x,\ \tau\ge n\}$ is determined by the walk up to time $n$ and the coins at times $<n$, and $\xi_{n,x}$ is independent of both.
-- source:
--   Hu, Obłój & Zhou, When to Quit Gambling, if You Must!, arXiv:2102.03157v1, p. 47, proof of Proposition A.3 (i) → (ii): P(S_{n−1} = x, τ ≥ n) = P(S_{τ∧(n−1)} = x) P(ξ_{n−1,x} = 1)

import Mathlib
import Definitions.Def_CasinoCPT_Embedding_Model

namespace CasinoCPT.Embedding

open MeasureTheory ProbabilityTheory

/-- p. 47 (proof of Proposition A.3, (i) ⇒ (ii)): for the randomized Root time
`τ = τ_R(b, r)` built from coins as in (7), the walk continues past time `n` from site `x`
exactly when it reached `(n, x)` unstopped and the coin `ξ_{n,x}` says "continue", and this
coin is independent of the past:
`P(S_n = x, τ ≥ n + 1) = P(S_n = x, τ ≥ n) · P(ξ_{n,x} = 1)`. -/
theorem rootTime_continue_factor {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration ℕ mΩ) (S : ℕ → Ω → ℤ) (ξ : Ω → ℝ) (hS : IsCasinoSpace P F S ξ)
    (b : ℤ → ℕ) (r : ℤ → ℝ) (coin : ℕ → ℤ → Ω → Bool) (hc : IsRootCoins P F b r coin)
    (n : ℕ) (x : ℤ) :
    P {ω | S n ω = x ∧ ((n + 1 : ℕ) : ℕ∞) ≤ rootTime S b coin ω} =
      P {ω | S n ω = x ∧ (n : ℕ∞) ≤ rootTime S b coin ω} * P {ω | coin n x ω = true} := by sorry

end CasinoCPT.Embedding
