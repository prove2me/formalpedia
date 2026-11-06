-- Prove2me | Theorems.Thm_ABPOnline_lemma_4_1
-- name    : ABPOnline.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:57:52.894575+00:00
-- url     : https://prove2.me/theorems/0a2c53cf-6ff8-4e8a-83b9-30c58d76cebf
-- title:
--   Lemma 4.1 (corrected: $c>0$) — nonnegative feasible control with slack, and its time rescaling
-- statement:
--   Let $B$ be a standard Brownian motion on $[0,1]$, $\kappa\in\mathbb R$, $c>0$ and $c^2>E_\star(\kappa)$. There exist $\rho>0$ and a nonnegative control $u$, progressively measurable with respect to the Brownian filtration, such that
--   $$
--   \|u\|_{\infty,2}<c,\qquad Y^u_1\ge\kappa+4\rho\ \text{a.s.}
--   $$
--   Moreover, for every $T<1$ sufficiently close to one, the rescaled control
--   $$
--   u^{(T)}_t:=T^{-1/2}u_{t/T},\qquad 0\le t\le T,
--   $$
--   driven by the rescaled Brownian motion $\tilde B_t:=\sqrt T\,B_{t/T}$, is progressively measurable for the completed natural filtration of $\tilde B$ and satisfies $\|u^{(T)}\|_{\infty,2}<c$ (norm on $(0,T)$) and $\tilde B_T+\int_0^Tu^{(T)}_t\,dt\ge\kappa+3\rho$ a.s.
--
--   This supplies the slack and the shortened horizon on which Algorithm 1 runs its first stage.
--
--   Differences from the source:
--   - generalization: E⋆(κ) defined from a standard Brownian motion B = (B_t)_{0≤t≤1} with its completed natural filtration → the statement holds for every process B with IsBrownianOn1 B P on every probability space, with E⋆ computed on that B; reason: E⋆(κ) depends only on the law of B; the source's Brownian motion is one such process
--   - correction: c ∈ ℝ with c² > E⋆(κ) → additionally 0 < c; reason: the printed lemma is false for c ≤ 0: with κ = 0 and c = −3, c² = 9 > 8 ≥ E⋆(0) by Lemma 2.3, but no u has ‖u‖_{∞,2} < −3; Proposition 4.8 applies the lemma with c = c_α > 0
--   - reading: Y^{u^(T)}_T for the rescaled control → the controlled process of u^(T) is driven by B̃_t = √T B_{t/T}, and u^(T) is progressive for the completed natural filtration of B̃; reason: the proof (p.11) uses √T Y^u_{t/T} = B̃_t + ∫₀ᵗ T^{−1/2}u_{s/T} ds; with the original B, u^(T)_t is F^B_{t/T}-measurable with t/T > t and is not a control
--   - encoding: "for every T < 1 sufficiently close to one" → ∃ T₀ < 1, ∀ T ∈ (T₀, 1); reason: the usual meaning
--   - encoding: ‖u‖_{∞,2} < c → (ess sup E u²_t)^{1/2} < c in ℝ≥0∞; u ≥ 0 at every time; reason: no junk value; nonnegativity off [0, 1] is harmless
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Lemma 4.1, (15), p.11 (PDF p.12)

import Mathlib
import Definitions.Def_ABPOnline_IsBrownianOn1
import Definitions.Def_ABPOnline_Estar

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ABPOnline

/-- **Lemma 4.1** (arXiv:2609.02124, printed p.11, PDF p.12), with `c > 0` added. Let `κ ∈ ℝ`,
`c > 0` and `c² > E⋆(κ)`. There exist `ρ > 0` and a nonnegative control `u`, progressively
measurable for the Brownian filtration, with `‖u‖_{∞,2} < c` and `Y^u_1 ≥ κ + 4ρ` a.s. Moreover, for
every `T < 1` sufficiently close to one, the rescaled control `u^{(T)}_t = T^{−1/2} u_{t/T}` (15)
satisfies `‖u^{(T)}‖_{∞,2} < c` (on `(0,T)`) and `Y^{u^{(T)}}_T ≥ κ + 3ρ` a.s., where the controlled
process of `u^{(T)}` is driven by the Brownian motion `B̃_t = √T B_{t/T}` of the proof.

**Formalization Note** "Sufficiently close to one" is `∃ T₀ < 1, ∀ T ∈ (T₀, 1)`. The rescaled
control is progressively measurable for the completed natural filtration of `B̃`, which is part
of the conclusion. -/
theorem lemma_4_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianOn1 B P) (κ c : ℝ) (hc : 0 < c)
    (hcE : Estar P B κ < ENNReal.ofReal (c ^ 2)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ u : ℝ≥0 → Ω → ℝ, (∀ t ω, 0 ≤ u t ω) ∧
      IsStronglyProgressive (brownFiltration P B) u ∧
      ctrlNormOn P 1 u < ENNReal.ofReal c ∧
      (∀ᵐ ω ∂P, κ + 4 * ρ ≤ ctrlTerminal B u 1 ω) ∧
      ∃ T₀ : ℝ, T₀ < 1 ∧ ∀ T : ℝ, T₀ < T → T < 1 →
        IsStronglyProgressive
            (brownFiltration P (fun t ω => Real.sqrt T * B (t / T.toNNReal) ω))
            (fun t ω => (Real.sqrt T)⁻¹ * u (t / T.toNNReal) ω) ∧
          ctrlNormOn P T (fun t ω => (Real.sqrt T)⁻¹ * u (t / T.toNNReal) ω) <
            ENNReal.ofReal c ∧
          ∀ᵐ ω ∂P, κ + 3 * ρ ≤ ctrlTerminal (fun t ω => Real.sqrt T * B (t / T.toNNReal) ω)
            (fun t ω => (Real.sqrt T)⁻¹ * u (t / T.toNNReal) ω) T ω := by sorry

end ABPOnline
