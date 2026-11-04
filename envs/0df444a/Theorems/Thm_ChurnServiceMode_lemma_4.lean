-- Prove2me | Theorems.Thm_ChurnServiceMode_lemma_4
-- name    : ChurnServiceMode.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:53:40.472604+00:00
-- url     : https://prove2.me/theorems/5738dc85-2e82-49e0-886a-980b16963e7a
-- title:
--   Lemma 4 — $\mathbb E[(1+|H_t|)e^{-\int_0^tQ}]\to0$ under finite interval policies
-- statement:
--   Assume $q>\mu_S$ (Assumption 1). For every starting satisfaction $x$ and every interval policy $\pi$ with finitely many intervals, under every control system started at $x$ that follows $\pi$,
--   $$\lim_{t\to\infty}\mathbb E\Bigl[(1+|H_t|)\,e^{-\int_0^tQ(H_s)\,ds}\Bigr]=0 .$$
--
--   This is Condition 6 of Proposition 2 for the policy of Theorem 1, which has at most three intervals.
--
--   Differences from the source:
--   - reading: Assumption 1 (q > µS), imposed "throughout this paper" (p.8) and not repeated in the statement → hypothesis μS < q; reason: standing assumption of the paper; the constant term of (11)–(12) divides by q − µS
--   - generalization: the limit (16) for the process H^{x,π} of the policy (on the paper's filtered space, specified uniquely in law) → the limit (16) for every π-feedback ControlSystem started at x, on any filtered probability space; reason: the paper's process is one such system, so the statement specializes to the paper's; it also covers solutions whose law is not unique (Lemma 1 correction)
--   - encoding: time t ≥ 0; continuous paths → time in ℝ≥0; every path of H and B continuous; reason: standard convention for continuous diffusions; same instances up to modification
--   - reading: σ_R (the Risky volatility; positivity never displayed) → 0 < σR (field of Params); reason: every formula of Lemmas 2–3 and Proposition 3 divides by σ_R, and σ_R is called a volatility
--   - reading: interval policy (Definition 2): "a countable number of alternating Risky and Safe intervals", Safe at each boundary point → IsIntervalPolicy π: the Risky set {π = R} is open and its frontier meets every bounded interval in finitely many points (a Safe interval may be a single point); reason: alternating intervals listed in order have no accumulating endpoints, and the proof of Lemma 1 (p.21) builds the process "inductively on the number of pieces of intervals"; openness of the Risky set is "Safe at each boundary point"
--   - encoding: interval policy "with a finite number of intervals" → HasFinitelyManyIntervals π: the frontier of {π = R} is finite; reason: finitely many alternating intervals ⇔ finitely many boundary points; same instances
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, Lemma 4, p.17 (PDF p.17); Assumption 1, p.8

import Mathlib
import Definitions.Def_ChurnServiceMode_ControlSystem

open MeasureTheory ProbabilityTheory Filter PeskirShiryaev.LocalTime
open scoped NNReal ENNReal Topology

namespace ChurnServiceMode

/-- **Lemma 4** (Kanoria, Lobel & Lu, *Managing Customer Churn via Service Mode Control*, SSRN 3188226 (Dec 1, 2022), p.17). Under Assumption 1 (`q > μS`, standing since p.8), for every
starting satisfaction `x` and every interval policy `π` with a finite number of intervals,
`lim_{t→∞} E[(1 + |H^{x,π}_t|) e^{−∫₀ᵗ Q(H^{x,π}_s) ds}] = 0`,
for every `π`-feedback control system started at `x`. -/
theorem lemma_4 (p : Params) (hq : p.μS < p.q) (π : ℝ → Mode) (hπ : IsIntervalPolicy π)
    (hfin : HasFinitelyManyIntervals π) (x : ℝ) (S : ControlSystem p x)
    (hS : S.IsFeedback π) :
    Tendsto (fun t : ℝ≥0 => ∫⁻ ω, ENNReal.ofReal ((1 + |S.H t ω|) * S.survival t ω) ∂S.P)
      atTop (𝓝 0) := by sorry

end ChurnServiceMode
