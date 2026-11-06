-- Prove2me | Theorems.Thm_FastMinority_lemma_3_5_one_step_growth
-- name    : FastMinority.lemma_3_5_one_step_growth
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:07:02.512257+00:00
-- url     : https://prove2.me/theorems/d14b02ff-a3e9-4c90-ab97-77ff458d722a
-- title:
--   Lemma 3.5 (proof sketch) — one-step growth in $\mathcal L$: $\Pr[X_{t+1}<(k/2)x]\le e^{-kx/24}+e^{-n/8}$
-- statement:
--   Let $X$ be the minority-size chain of MINORITY with $n$ agents and odd sample size $k$, and let $L=\lceil n/(4k)\rceil$. For every state $1\le x<L$,
--   $$
--   \Pr\Big[X_{t+1}<\frac k2\,x\ \Big|\ X_t=x\Big]\le e^{-kx/24}+e^{-n/8}.
--   $$
--
--   In the lower region the minority size thus multiplies by at least $k/2$ in one round, except with exponentially small probability. Iterated over $\lceil\log L/\log(k/2)\rceil$ rounds this gives Lemma 3.5.
--
--   **Formalization Note** The bound is the one of the proof sketch on p.9, which Claims 5.3 and 5.4 (p.20) prove; the display (5.4) on p.19 states the weaker $e^{-k/24}+e^{-n/12}$. The event is the set of next states $s$ with $s<kx/2$ under the published kernel.
--
--   Differences from the source:
--   - generalization: standing assumption k = Θ(log² n) → every n and every odd k; reason: the bound is explicit and its proof (Claims 5.3, 5.4) holds for every configuration with kx/n < 1/4; specializes to the band
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Lemma 3.5, proof sketch, p.9 (PDF p.11); Claims 5.3–5.4, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_MinorityDynamics_Chain
import Definitions.Def_FastMinority_lowerRegion

set_option autoImplicit false

open Classical

namespace FastMinority

/-- **One-step growth in the lower region** (proof sketch of Lemma 3.5, Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), p.9 = PDF p.11):
for a state `1 ≤ x < L`, `Pr[X_{t+1} < (k/2)·x | X_t = x] ≤ e^{−kx/24} + e^{−n/8}`.

**Formalization Note** The chain's step is the published `MinorityDynamics.actualKernel n k`; the event
is the set of next states `s` with `s < kx/2` (real comparison). Stated for every `n` and every odd `k`
(the bound is explicit and non-asymptotic). -/
theorem lemma_3_5_one_step_growth (n k : ℕ) (hk : Odd k) (x : Fin (n + 1))
    (hx : x ∈ lowerRegion n k) :
    ∑ s ∈ Finset.univ.filter (fun s : Fin (n + 1) => ((s : ℕ) : ℝ) < (k : ℝ) * (x : ℕ) / 2),
        MinorityDynamics.actualKernel n k x s ≤
      Real.exp (-((k : ℝ) * (x : ℕ)) / 24) + Real.exp (-(n : ℝ) / 8) := by sorry

end FastMinority
