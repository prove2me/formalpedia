-- Prove2me | Theorems.Thm_FastMinority_proposition_3_2
-- name    : FastMinority.proposition_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:07:59.479293+00:00
-- url     : https://prove2.me/theorems/e2537916-b3c7-4406-b517-03ef9b8031b9
-- title:
--   Proposition 3.2 — from $\mathcal H^+$, consensus in one step with probability $\ge e^{-8b}$
-- statement:
--   Let $X$ be the minority-size chain of MINORITY with $n$ agents and odd sample size $k$, let $b>0$, and let $\mathcal H^+=\mathcal H\cup\{0\}$, where $\mathcal H=\{x>0:\mathbb E[X_{t+1}\mid X_t=x]\le b\}$ is the set of good states. Then for every $x\in\mathcal H^+$,
--   $$
--   \Pr\big[X_{t+1}=0\mid X_t=x\big]\ge e^{-8b}.
--   $$
--
--   Every visit to $\mathcal H^+$ is therefore an attempt at consensus that succeeds with a probability bounded below by a constant; this is what makes the hitting time of $\mathcal H^+$ control the consensus time.
--
--   **Formalization Note** The chain's step is the published kernel `MinorityDynamics.actualKernel n k`.
--
--   Differences from the source:
--   - generalization: standing assumption k = Θ(log² n), the fixed constant b → every n, every odd k and every b > 0; reason: the proof uses only n ≥ 2 (n ≤ 1 is immediate) and that the folded adoption probability is at most 1/2; specializes to the paper's n, k, b
--   - reading: H is both the good set (3.1) and the interval [M′+1, R′−1], with M′ and R′ undefined → H = the good set (3.1); reason: Section 3.1 recalls H⁺ by (3.1), and the proof uses only E[X_{t+1} | X_t = x] ≤ b
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Proposition 3.2, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_MinorityDynamics_Chain
import Definitions.Def_FastMinority_goodPlus

set_option autoImplicit false

open Classical

namespace FastMinority

/-- **Proposition 3.2** (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), p.8 = PDF p.10): from every state of `𝓗⁺` (a good state, or
consensus), the next state is consensus with probability at least `e^{−8b}`:
`Pr[X_{t+1} = 0 | X_t = x] ≥ e^{−8b}` for `x ∈ 𝓗⁺`.

**Formalization Note** The chain's step is the published `MinorityDynamics.actualKernel n k`. Stated for
every `n`, every odd `k` and every `b > 0` (the proof uses only `n ≥ 2` and that the minority-adoption
probability is at most `1/2` after folding). -/
theorem proposition_3_2 (n k : ℕ) (hk : Odd k) (b : ℝ) (hb : 0 < b) (x : Fin (n + 1))
    (hx : x ∈ goodPlus n k b) :
    Real.exp (-8 * b) ≤ MinorityDynamics.actualKernel n k x 0 := by sorry

end FastMinority
