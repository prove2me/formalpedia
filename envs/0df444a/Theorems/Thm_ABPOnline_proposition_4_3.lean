-- Prove2me | Theorems.Thm_ABPOnline_proposition_4_3
-- name    : ABPOnline.proposition_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:58:04.399804+00:00
-- url     : https://prove2.me/theorems/330bdaae-399a-456b-8750-89b612ab4fc7
-- title:
--   Proposition 4.3 — approximation by simple predictable controls of the form in Definition 4.2
-- statement:
--   Let $T>0$ be rational and $B$ a standard Brownian motion on $[0,T]$. Suppose $u\ge0$ on $[0,T]$ is progressively measurable with respect to the Brownian filtration, $\|u\|_{\infty,2}<c$ (on $(0,T)$), and $Y^u_T\ge a$ almost surely. Let $2\le p<\infty$ and $\varepsilon>0$. Then there is a bounded nonnegative simple predictable control $\beta$ of the form in Definition 4.2 such that
--   $$
--   \|\beta\|_{\infty,2}<c,\qquad \|(a-Y^\beta_T)_+\|_{L^p}<\varepsilon .
--   $$
--
--   Feasible Brownian controls with a strict norm bound can thus be replaced by controls computable from finitely many past Brownian values, without regularity of an optimizer.
--
--   Differences from the source:
--   - reading: T unspecified (the horizon of u) → T a positive rational; reason: Definition 4.2 requires s_L = T rational, so for irrational T no control of that form exists; Algorithm 1 takes T ∈ (0, 1) rational
--   - encoding: Brownian filtration on [0, T]; ‖·‖_{∞,2} on [0, T]; L^p norm → completed natural filtration of B; ess sup over (0, T) in ℝ≥0∞; eLpNorm with exponent p; reason: the same quantities without junk values
--   - encoding: rational piecewise-polynomial F_j → finitely many closed rational polyhedra covering ℝ^m with a rational polynomial on each; reason: the standard meaning, which covers the approximants built in the proof
--   - encoding: B a Brownian motion on [0, T] → t ↦ T^{-1/2} B_{Tt} satisfies IsBrownianOn1 (standard Brownian motion on [0, 1]); reason: Brownian scaling, the same processes on [0, T]; values of B after T are unconstrained and never used
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Proposition 4.3, (17), p.12 (PDF p.13)

import Mathlib
import Definitions.Def_ABPOnline_IsBrownianOn1
import Definitions.Def_ABPOnline_Estar
import Definitions.Def_ABPOnline_SimpleCtrl

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ABPOnline

/-- **Proposition 4.3** (arXiv:2609.02124, printed p.12, PDF p.13). Suppose `u ≥ 0` is
progressively measurable with respect to the Brownian filtration on `[0,T]`, `‖u‖_{∞,2} < c`, and
`Y^u_T ≥ a` almost surely. Let `2 ≤ p < ∞` and `ε > 0`. Then there is a bounded nonnegative simple
predictable control `β` of the form in Definition 4.2 such that `‖β‖_{∞,2} < c` and
`‖(a − Y^β_T)₊‖_{L^p} < ε` (17).

**Formalization Note** `T` is a positive rational, as Definition 4.2 (`s_L = T` rational) and
Algorithm 1 (`T ∈ (0,1)` rational) require. "`B` is a standard Brownian motion on `[0,T]`" is
written through Brownian scaling: `t ↦ T^{-1/2} B_{Tt}` is a standard Brownian motion on `[0,1]`
(`IsBrownianOn1`); only the values of `B` on `[0,T]` are constrained. The norms are on `(0,T)`;
`β_t` is driven by the same Brownian motion `B`. -/
theorem proposition_4_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (T : ℚ) (hT : 0 < T)
    (hB : IsBrownianOn1 (fun t ω => (Real.sqrt T)⁻¹ * B ((T : ℝ).toNNReal * t) ω) P)
    (u : ℝ≥0 → Ω → ℝ) (hu0 : ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ ω, 0 ≤ u t ω)
    (hu : IsStronglyProgressive (brownFiltration P B) u) (c a : ℝ)
    (hnorm : ctrlNormOn P T u < ENNReal.ofReal c)
    (hY : ∀ᵐ ω ∂P, a ≤ ctrlTerminal B u T ω) (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) :
    ∃ β : SimpleCtrl, β.IsValidOn T ∧
      ctrlNormOn P T (β.proc B) < ENNReal.ofReal c ∧
      eLpNorm (fun ω => max (a - ctrlTerminal B (β.proc B) T ω) 0) (ENNReal.ofReal p) P <
        ENNReal.ofReal ε := by sorry

end ABPOnline
