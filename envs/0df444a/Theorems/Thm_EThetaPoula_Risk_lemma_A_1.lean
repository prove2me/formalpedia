-- Prove2me | Theorems.Thm_EThetaPoula_Risk_lemma_A_1
-- name    : EThetaPoula.Risk.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:32.092998+00:00
-- url     : https://prove2.me/theorems/bd7095f0-986d-481c-a04b-157f5a3a3cc8
-- title:
--   Lemma A.1, p.31 — the tamed coordinates are $O(\lambda^{-1/2})$
-- statement:
--   Under Assumption 3, for $\theta\in\mathbb R^d$, $x\in\mathbb R^m$, $0<\lambda\le1$, $i=1,\dots,d$, and $0<\varepsilon<1$,
--   $$
--   |G^{(i)}_\lambda(\theta,x)|\le2\lambda^{-1/2},\qquad|F^{(i)}_\lambda(\theta,x)|\le\lambda^{-1/2}(1+|x|)^\rho\,(K_F+K_F|\theta^{(i)}|).
--   $$
--
--   The bound on $G_\lambda$ holds for any $G$, because of the componentwise taming, and is the reason that $G$ needs no pointwise regularity in the moment estimates.
--
--   Differences from the source: none.
-- source:
--   Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, Lemma A.1, (69), p.31

import Mathlib
import Definitions.Def_EThetaPoula_Risk_Model
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EThetaPoula.Risk

/-- **Lemma A.1**, Lim, Neufeld, Sabanis, Zhang, arXiv:2210.13193v3, p.31: under Assumption 3, for
`0 < λ ≤ 1`, the coordinates of (7) satisfy (69): `|G^{(i)}_λ(θ, x)| ≤ 2λ^{−1/2}` and
`|F^{(i)}_λ(θ, x)| ≤ λ^{−1/2} (1 + |x|)^ρ (K_F + K_F |θ^{(i)}|)`. The `ε` of (7) ranges over
`(0, 1)`. -/
theorem lemma_A_1 {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (S : Model d m Ω)
    (C : AssumptionData d m) (h3 : S.Assumption3 C) (ε : ℝ) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (lam : ℝ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (θ : Eucl d) (x : Eucl m) (i : Fin d) :
    |S.Glam lam ε θ x i| ≤ 2 * lam ^ (-(1 / 2 : ℝ)) ∧
    |S.Flam lam θ x i| ≤ lam ^ (-(1 / 2 : ℝ)) * (1 + ‖x‖) ^ S.ρ * (C.KF + C.KF * |θ i|) := by sorry

end EThetaPoula.Risk
