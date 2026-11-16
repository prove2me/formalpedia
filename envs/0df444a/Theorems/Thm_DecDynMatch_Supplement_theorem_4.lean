-- Prove2me | Theorems.Thm_DecDynMatch_Supplement_theorem_4
-- name    : DecDynMatch.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:34:38.386366+00:00
-- url     : https://prove2.me/theorems/8768ef82-f7b5-4418-a4b8-cd4908d153ad
-- title:
--   Theorem 4 — SC-PC under two-sided learning: $\mathbb E[D(T;I)]=O(t^*+K^4\Delta_{\min}^{-2}\log T)$
-- statement:
--   In the two-sided learning setting neither players nor arms know their utilities: when player $i$ and arm $k$ are matched they observe stochastic utilities in $[0,1]$ whose means, conditional on all past actions and observations and on the current proposals and acceptance decisions, are $\mu_{i,k}$ and $\pi_{k,i}$. SC-PC (Self-Calibrating Preference Certification, App. C.1) is run by every player and every arm, each arm using a fixed private order of proposers.
--
--   There is one absolute constant $C$ such that for every $K\ge2$, every dynamic matching instance $I$ with mean utilities in $[0,1]$ and last population-event time $t^*$, every choice of the arms' private orders, every admissible reward process and every horizon $T\ge1$,
--   $$
--   \mathbb E[D(T;I)]\le C\Bigl(t^*+\frac{K^4}{\Delta_{\min}^{2}}\log T\Bigr),
--   $$
--   where $D(T;I)$ counts the rounds $1\le t\le T$ in which the realized matching differs from the player-optimal stable matching of the true means, and $\Delta_{\min}$ is the minimum utility gap of the final market (11).
--
--   The $\Delta_{\min}^{-2}\log T$ dependence matches the static learning lower bound of Claim 1, so preference learning alone accounts for the asymptotic term.
--
--   **Formalization Note** The protocol is `Mpc` (Algorithms 2–7 and (46)–(51) transcribed), the reward hypothesis is `RewardOK`, the expectation is `expDpc` and the gap is `deltaMin`. $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: E[D(T; I)] = O(t* + K⁴ Δ_min^{−2} log T) → ∃ C, ∀ K ι I ord Ω P X Y, RewardOK → ∀ T ≥ 1, expDpc ≤ C (t* + K⁴ (Δ_min²)⁻¹ log T); reason: one constant for all parameters, instances and reward processes (p.51, eq. (70)); natural log changes only C
--   - encoding: stochastic utilities with conditional means μ_{i,k}, π_{k,i} given H_t → potential-outcome tables X, Y with values in [0, 1], measurable, and set-integral identity on A ∩ {matched} for A in the σ-algebra of the observation record through t − 1; reason: SC-PC is deterministic given observations, so that record generates H_t; unobserved entries can be set to 0
--   - encoding: E[D(T; I)] → Σ_{t=1}^{T} P(M_t is not a POSM), with P of a set its outer measure; reason: linearity of expectation; outer measure equals the probability on measurable events and avoids a junk value
--   - encoding: Δ_min for an empty final market (undefined; bound D ≤ min{T, t* − 1}) → deltaMin I = 0, so (Δ_min²)⁻¹ = 0; reason: only excludes the undefined case; the paper's bound for an empty final market has no gap term (p.51)
--   - encoding: each arm's fixed private order ≺ → an injective rank ord k : ι → ℕ, universally quantified; reason: every strict total order on a finite set is induced by such a rank
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), Theorem 4, p.12; eq. (11), p.12; App. C.1, pp.29–35; App. C.6, pp.50–51

import Mathlib
import Definitions.Def_DecDynMatch_Supplement_UnitUtilities
import Definitions.Def_DecDynMatch_Supplement_RewardOK
import Definitions.Def_DecDynMatch_Supplement_deltaMin

namespace DecDynMatch.Supplement

open DecDynMatch MeasureTheory

universe u v

/-- **Theorem 4 (Two-sided learning and dynamic POSM).** J. Chen, M. Gao, Z. Zhang, *Decentralized
Dynamic Stable Matching*, arXiv:2610.41912 (held version, sha256 6a27277e…), Theorem 4, p.12: "In
the two-sided learning setting, for every K ≥ 2, every dynamic matching instance I, and time horizon
T ≥ 1, SC-PC satisfies E[D(T; I)] = O(t* + K⁴ Δ_min^{−2} log T)."

There is one absolute constant `C` such that for every `K`, every finite player type `ι`, every
instance `I` with (mean) utilities in `[0, 1]`, every choice of the arms' private orders, every
probability space carrying an admissible reward process and every `T ≥ 1`, the expected number of
rounds `1 ≤ t ≤ T` in which SC-PC's realized matching is not the POSM (of the true means) is at most
`C (t* + K⁴ Δ_min^{−2} log T)`.

**Formalization Note.** `C` is chosen before everything else (p.51: "one constant for all
admissible parameters, instances, and reward processes"; eq. (70)). `log` is the natural logarithm
(a change of base changes only `C`); `log 1 = 0`. `Δ_min^{−2}` is `(deltaMin I ^ 2)⁻¹`, which is `0`
when the final market is empty (then `deltaMin I = 0`). The private orders are arbitrary injective
ranks, not the utility rankings. -/
theorem theorem_4 :
    ∃ C : ℝ, ∀ (K : ℕ) (ι : Type u) [Fintype ι] (I : Instance K ι), UnitUtilities I →
      ∀ (ord : Fin K → ι → ℕ), (∀ k, Function.Injective (ord k)) →
      ∀ (Ω : Type v) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : ℕ → ι → Fin K → Ω → ℝ) (Y : ℕ → Fin K → ι → Ω → ℝ), RewardOK I ord P X Y →
      ∀ T : ℕ, 1 ≤ T →
        expDpc I ord P X Y T ≤
          C * ((tstar I : ℝ) + (K : ℝ) ^ 4 * (deltaMin I ^ 2)⁻¹ * Real.log (T : ℝ)) := by sorry

end DecDynMatch.Supplement
