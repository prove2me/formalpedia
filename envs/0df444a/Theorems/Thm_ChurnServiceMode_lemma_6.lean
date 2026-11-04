-- Prove2me | Theorems.Thm_ChurnServiceMode_lemma_6
-- name    : ChurnServiceMode.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:53:39.628549+00:00
-- url     : https://prove2.me/theorems/7207620d-2016-4d67-93ab-14dd0c12815a
-- title:
--   Lemma 6 — local times exist; no time in a countable set while Risky
-- statement:
--   For every control system started at any $x$ (any admissible policy):
--   1. the satisfaction process $H$ has a finite symmetric local time $L^H(t,y)$ at every level $y\in\mathbb R$;
--   2. for every countable set $E\subseteq\mathbb R$ and every $t\ge0$, almost surely
--   $$\int_0^t\mathbb 1\{H_s\in E\ \text{and}\ u_s\ne S\}\,ds=0 .$$
--
--   The second statement is what lets the Itô–Tanaka formula (10) ignore the countable set where the candidate value function is not twice differentiable.
--
--   **Formalization Note** The symmetric local time at level $y$ is the limit in probability of $(2\varepsilon)^{-1}\int_0^t\mathbb 1\{|H_s-y|<\varepsilon\}\,d\langle H\rangle_s$ (the published `HasCurveLocalTime` at the constant curve $y$), with the clock a bracket of the martingale part of $H$. A real-valued local time is finite, so the paper's "$L^H(t,y)<\infty$ almost surely" is its existence.
--
--   Differences from the source:
--   - generalization: admissible policies π ∈ Π of Definition 1 (adapted control on the given filtered space, processes specified uniquely in law, integrals of (7) existing) → every ControlSystem: any filtered probability space carrying a standard Brownian motion, a progressively measurable {R,S}-valued control and a continuous adapted solution of (3) (weak formulation; uniqueness in law not required); reason: every admissible policy gives such a system (progressive measurability is what makes the integrals of (1) exist), so the class contains Π and the statement specializes to the paper's
--   - encoding: symmetric local time (Salins–Spiliopoulos Def. A.1, Tanaka form); "L^H(t, y) < ∞ a.s." → real-valued local time defined by the occupation limit HasCurveLocalTime with a bracket clock; its existence; reason: for continuous semimartingales the two definitions agree (occupation-times formula); a real value is finite
--   - encoding: time t ≥ 0; continuous paths → time in ℝ≥0; every path of H and B continuous; reason: standard convention for continuous diffusions; same instances up to modification
--   - reading: σ_R (the Risky volatility; positivity never displayed) → 0 < σR (field of Params); reason: every formula of Lemmas 2–3 and Proposition 3 divides by σ_R, and σ_R is called a volatility
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, Lemma 6, p.21 (PDF p.21)

import Mathlib
import Definitions.Def_ChurnServiceMode_ControlSystem
import Definitions.Def_PeskirShiryaev_LocalTime_Curve

open MeasureTheory ProbabilityTheory Filter PeskirShiryaev.LocalTime
open scoped NNReal ENNReal Topology

namespace ChurnServiceMode

/-- **Lemma 6** (Kanoria, Lobel & Lu, *Managing Customer Churn via Service Mode Control*, SSRN 3188226 (Dec 1, 2022), p.21). For every control system started at any `x`:
the satisfaction process `H` has a (finite, real-valued) symmetric local time `L^H(t, y)` at every
level `y`; and for every countable set `E ⊆ ℝ` and every `t ≥ 0`,
`∫₀ᵗ 1{H_s ∈ E and u_s ≠ S} ds = 0` almost surely.

**Formalization Note.** The local time is the published `HasCurveLocalTime` at the constant curve
`y`, i.e. the limit in probability of `(2ε)⁻¹ ∫₀ᵗ 1{|H_s − y| < ε} d⟨H⟩_s`, where the clock is a
bracket of the martingale part `M` of `H` (equal to `⟨H⟩`). A real-valued local time is finite, so
"`L^H(t, y) < ∞` a.s." is its existence. -/
theorem lemma_6 (p : Params) (x : ℝ) (S : ControlSystem p x) :
    (∃ Qc : IncreasingClock S.Ω, HasBracket S.P S.ℱ S.M Qc ∧
      ∀ y : ℝ, ∃ L : IncreasingClock S.Ω, HasCurveLocalTime S.P S.ℱ S.H Qc (fun _ => y) L) ∧
    ∀ E : Set ℝ, E.Countable → ∀ t : ℝ≥0, ∀ᵐ ω ∂S.P,
      ∫ s in (0 : ℝ)..(t : ℝ),
        Set.indicator {r : ℝ | S.H r.toNNReal ω ∈ E ∧ S.u r.toNNReal ω ≠ Mode.S}
          (fun _ => (1 : ℝ)) s = 0 := by sorry

end ChurnServiceMode
