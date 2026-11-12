-- Prove2me | Theorems.Thm_DIObliviousTransfer_lemma_31
-- name    : DIObliviousTransfer.lemma_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T09:05:55.202998+00:00
-- url     : https://prove2.me/theorems/91dd2b3e-166c-44ea-8ec4-c6a2b146121a
-- title:
--   Lemma 31 — constant-density bucketing
-- statement:
--   Fix $\delta_*\in(0,1)$ and $0<r_{\min}\le r_{\max}\le1$. Then there is $\eta_0>0$ such that for every $\eta\in(0,\eta_0)$ there is $c>0$ with the following property, for all large $n$ and every strategy with a pre-late-question selector $K$:
--   $$\Pr\Big[r_{\min}n\le|K|\le r_{\max}n,\ \sum_jL_j\le\eta n,\ \sum_{j\in K}W_j\ge|K|-\eta n\Big]\le2^{-cn}.$$
--
--   Applied on $[0.047/56,1]$ with $\delta_*=1/2$, it fixes the constants $\gamma,\eta_{\mathrm{MS}}$ of the schedule.
--
--   Differences from the source:
--
--   - encoding: quantum systems and strategies in the abstract (registers, measurements, instruments) → finite-dimensional registers, matrices over finite types, POVMs and Kraus instruments; reason: Decision D2: registers are polynomial-size or finite-alphabet throughout; same instances
--   - reading: for sufficiently small constants h, η > 0, cover [r_min n, r_max n] by intervals …; if η < min_j η_sel(ρ_j, g_j), then ∃c > 0, n₀ → ∃ η₀ > 0, ∀ η ∈ (0, η₀), ∃ c > 0, SelectorBound δ r_min r_max c η; reason: the cover, h and g_j are devices of the proof; the formal content is the bound for all sufficiently small η
--   - encoding: a pre-late-question selector K → K = {j : J_j = 1}, frozen by Dave's first-round instrument; reason: the selector of G^sel is exactly such a set
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Lemma 31, p.68 (PDF p.70)

import Mathlib
import Definitions.Def_DIObliviousTransfer_SelectorBound

namespace DIObliviousTransfer

/-- **Lemma 31 (Constant-density bucketing)**, Batra, Chen, Jain, Zhang, arXiv:2610.01421 (held
version, sha256 8334c039…), p.68 (PDF p.70). Fix `0 < r_min ≤ r_max ≤ 1` and `δ∗ ∈ (0, 1)`. For
every sufficiently small loss threshold `η > 0` there are `c > 0` and `n₀` such that every allowed
strategy with a pre-late-question selector `K` satisfies, for `n ≥ n₀`,
`Pr[r_min n ≤ |K| ≤ r_max n, Σ_j L_j ≤ ηn, Σ_{j ∈ K} W_j ≥ |K| − ηn] ≤ 2^{−cn}`.

**Formalization Note** (decision D2, and a reading). The selector `K` is the set of copies with
`J_j = 1`, frozen in the first round before `C` is sampled. The cover, `h` and the `g_j` of the
printed statement are devices of the proof; the statement asserts the bound for all `η` below a
positive threshold, with the exponent `c` chosen after `η` (`SelectorBound`). -/
theorem lemma_31 (δ rmin rmax : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (h0 : 0 < rmin)
    (h1 : rmin ≤ rmax) (h2 : rmax ≤ 1) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ c : ℝ, 0 < c ∧ SelectorBound δ rmin rmax c η := by sorry

end DIObliviousTransfer
