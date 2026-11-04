-- Prove2me | Theorems.Thm_ChurnServiceMode_proposition_1
-- name    : ChurnServiceMode.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:53:51.181678+00:00
-- url     : https://prove2.me/theorems/af8eda6b-9086-4016-b169-28932e52cb4f
-- title:
--   Proposition 1 — finite expected lifetime and CLV under finite interval policies
-- statement:
--   Assume $q>\mu_S$ (Assumption 1). For every starting satisfaction $x$ and every interval policy $\pi$ with finitely many intervals, both the customer lifetime and the CLV are finite: under every control system started at $x$ that follows $\pi$,
--   $$\mathbb E[T^{x,\pi}]<\infty\qquad\text{and}\qquad V(x,\pi)<\infty .$$
--
--   Under Assumption 1 the satisfaction process cannot stay satisfied forever, which is what makes the control problem well posed.
--
--   Differences from the source:
--   - generalization: E[T] < ∞ and V(x, π) < ∞ for the process H^{x,π} of the policy (on the paper's filtered space, specified uniquely in law) → E[T] < ∞ and V(x, π) < ∞ for every π-feedback ControlSystem started at x, on any filtered probability space; reason: the paper's process is one such system, so the statement specializes to the paper's; it also covers solutions whose law is not unique (Lemma 1 correction)
--   - reading: CLV (7): E[∫₀^∞ µ_{u_t} 1{t<T} dt + ∫₀^∞ σ_{u_t} 1{t<T} dB_t] → clv := E[∫₀^∞ µ_{u_t} 1{t<T} dt] in [0, ∞] on P ⊗ U[0,1], T as in (6) with inf ∅ = ∞; reason: footnote 6 (p.7) drops the stochastic integral as having zero expectation; the remaining term is what (9) and the proofs use
--   - encoding: time t ≥ 0; continuous paths → time in ℝ≥0; every path of H and B continuous; reason: standard convention for continuous diffusions; same instances up to modification
--   - reading: σ_R (the Risky volatility; positivity never displayed) → 0 < σR (field of Params); reason: every formula of Lemmas 2–3 and Proposition 3 divides by σ_R, and σ_R is called a volatility
--   - reading: interval policy (Definition 2): "a countable number of alternating Risky and Safe intervals", Safe at each boundary point → IsIntervalPolicy π: the Risky set {π = R} is open and its frontier meets every bounded interval in finitely many points (a Safe interval may be a single point); reason: alternating intervals listed in order have no accumulating endpoints, and the proof of Lemma 1 (p.21) builds the process "inductively on the number of pieces of intervals"; openness of the Risky set is "Safe at each boundary point"
--   - encoding: interval policy "with a finite number of intervals" → HasFinitelyManyIntervals π: the frontier of {π = R} is finite; reason: finitely many alternating intervals ⇔ finitely many boundary points; same instances
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, Proposition 1, p.8 (PDF p.8); Assumption 1, p.8

import Mathlib
import Definitions.Def_ChurnServiceMode_ControlSystem

open MeasureTheory ProbabilityTheory Filter PeskirShiryaev.LocalTime
open scoped NNReal ENNReal Topology

namespace ChurnServiceMode

/-- **Proposition 1** (Kanoria, Lobel & Lu, *Managing Customer Churn via Service Mode Control*, SSRN 3188226 (Dec 1, 2022), p.8). Under Assumption 1 (`q > μS`), for every `x` and every
interval policy `π` with a finite number of intervals, the customer lifetime and the CLV are
finite: `E[T^{x,π}] < ∞` and `V(x, π) < ∞`, for every `π`-feedback control system started
at `x`. -/
theorem proposition_1 (p : Params) (hq : p.μS < p.q) (π : ℝ → Mode) (hπ : IsIntervalPolicy π)
    (hfin : HasFinitelyManyIntervals π) (x : ℝ) (S : ControlSystem p x)
    (hS : S.IsFeedback π) :
    S.expectedLifetime < ⊤ ∧ S.clv < ⊤ := by sorry

end ChurnServiceMode
