-- Prove2me | Theorems.Thm_CarbonFBSDE_MultiPeriod_proposition_3_5_iii
-- name    : CarbonFBSDE.MultiPeriod.proposition_3_5_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:20:29.560982+00:00
-- url     : https://prove2.me/theorems/4e604396-d2b4-442f-83d1-58bd2f58762f
-- title:
--   Proposition 3.5 (iii), p. 15 — comparison: φ ≤ φ̃ in 𝒦 implies v ≤ ṽ
-- statement:
--   Let Assumption 1 hold, $r\in\mathbb R$ and $\tau>0$. Let $\varphi,\tilde\varphi\in\mathcal K$ with $\tilde\varphi(p,e)\ge\varphi(p,e)$ for every $(p,e)\in\mathbb R^d\times\mathbb R$, and let $v$, $\tilde v$ be the value functions of Proposition 3.2 for the terminal conditions $\varphi$ and $\tilde\varphi$. Then
--   $$\tilde v(t,p,e)\ge v(t,p,e)\qquad\text{for every }(t,p,e)\in[0,\tau)\times\mathbb R^d\times\mathbb R.$$
--
--   The comparison property is what makes the diagonal $e\mapsto v^\Phi(t,p,e,e)$ monotone in Lemma 3.13.
--
--   **Formalization Note** "$v$ is the value function of Proposition 3.2" is the hypothesis that $v$ is a value function for $\varphi$ in the sense of the Model file: solutions exist from every $(t_0,p,e)$ with $t_0<\tau$ and all have $Y_{t_0}=v(t_0,p,e)$ a.s.
-- source:
--   Chassagneux, Chotai & Crisan, Modelling multi-period carbon markets using singular forward-backward SDEs, arXiv:2008.09044v1, p. 15, Proposition 3.5 (iii)

import Mathlib
import Definitions.Def_CarbonFBSDE_MultiPeriod_Model

open MeasureTheory ProbabilityTheory Filter Set EthierKurtz
open scoped NNReal ENNReal Topology

namespace CarbonFBSDE.MultiPeriod

theorem proposition_3_5_iii {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (B : Basis d Ω)
    (hB : B.Valid) (c : Coeffs d) (L l1 l2 : ℝ) (hA : Assumption1 c L l1 l2) (r : ℝ)
    (τ : ℝ≥0) (hτ : 0 < τ) (φ φt : SDEState d → ℝ → ℝ) (Lφ Lφt : ℝ)
    (hφ : InK φ Lφ) (hφt : InK φt Lφt) (hle : ∀ p e, φ p e ≤ φt p e)
    (v vt : ℝ≥0 → SDEState d → ℝ → ℝ)
    (hv : IsValueFn₀ B c r φ τ v) (hvt : IsValueFn₀ B c r φt τ vt) :
    ∀ t < τ, ∀ (p : SDEState d) (e : ℝ), v t p e ≤ vt t p e := by sorry

end CarbonFBSDE.MultiPeriod
