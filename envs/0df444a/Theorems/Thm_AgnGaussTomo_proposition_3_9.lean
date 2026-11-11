-- Prove2me | Theorems.Thm_AgnGaussTomo_proposition_3_9
-- name    : AgnGaussTomo.proposition_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:25:43.259191+00:00
-- url     : https://prove2.me/theorems/be58353c-7680-4933-808c-96dc06f77012
-- title:
--   Proposition 3.9 — near-vacuum geometry of the infidelity objective
-- statement:
--   1. There are universal constants $r_0,C>0$ such that for every $n$, every density operator $\rho$ and every $\theta\in B_{r_0}=\{\theta\in\mathcal P_n:\|\theta\|_{\mathcal P}\le r_0\}$,
--   $$
--   \|\nabla^2f_\rho(\theta)-2I\|_{\mathrm{op}}\le C\big(\|\theta\|_{\mathcal P}+d_{\mathrm{tr}}(\rho,|0\rangle\langle0|)\big),
--   $$
--   where $f_\rho(\theta)=1-\langle\psi(\theta)|\rho|\psi(\theta)\rangle$ and the operator norm is induced by $\|\cdot\|_{\mathcal P}$.
--   2. There are universal constants $\gamma_0>0$ and $R\in(0,1/16)$ such that, for every $n$ and every density operator $\rho$ with $d_{\mathrm{tr}}(\rho,|0\rangle\langle0|)\le\gamma_0$,
--   $$
--   I\preceq\nabla^2f_\rho(\theta)\preceq3I\qquad(\theta\in B_R),
--   $$
--   and $f_\rho$ has a unique minimizer $\theta_*$ over $B_R$, which satisfies $\|\theta_*\|_{\mathcal P}\le R/4$.
--
--   Near the vacuum the infidelity objective is smooth and strongly convex, uniformly in $n$, so gradient descent converges to its minimizer.
--
--   Differences from the source:
--   - reading: r₀, C, γ₀ and R → universal constants chosen before n and every other parameter; reason: the paper calls them universal constants; ≲ and O hide absolute constants
--   - encoding: B_r and ∇²f_ρ → the closed ball of radius r in Pspace n and the derivative of Mathlib's gradient; I ⪯ H ⪯ 3I as ‖h‖² ≤ ⟨h, Hh⟩ ≤ 3‖h‖²; reason: the norm and inner product of Pspace n are ‖·‖_P and ⟨·,·⟩_P (Eq. (12))
--   - reading: its unique minimizer θ_∗ over B_R satisfies ‖θ_∗‖_P ≤ R/4 → a minimizer over B_R exists, is unique, and has norm at most R/4; reason: the definite article asserts existence and uniqueness
--   - encoding: trace distances → the published BosonicLearn.traceDist (½‖·‖₁) in ℝ≥0∞, compared with ENNReal.ofReal of the bound; reason: same values on density operators
-- source:
--   Arulandu, Chen, Chen, Li, Ma, Finding Gaussian Structure in Bosonic States, arXiv:2610.06810 (version of 3 Nov 2026), Proposition 3.9, printed p. 19 (PDF p. 22); proof on pp. 20–22

import Mathlib
import Definitions.Def_BosonicLearn_traceDist
import Definitions.Def_AgnGaussTomo_vacuum
import Definitions.Def_AgnGaussTomo_fobj

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace AgnGaussTomo

/-- **Proposition 3.9: near-vacuum geometry of the infidelity objective.** Arulandu, Chen, Chen, Li, Ma,
*Finding Gaussian Structure in Bosonic States*, arXiv:2610.06810 (version of 3 Nov 2026), Proposition
3.9, printed p. 19 (PDF p. 22): "There exist universal constants r₀, C > 0 such that for every n,
every density operator ρ, and every θ ∈ B_{r₀}, ‖∇²f_ρ(θ) − 2I‖_op ≤ C(‖θ‖_P + d_tr(ρ, |0⟩⟨0|)). (23)
where the operator norm is induced by ‖·‖_P. In particular, there are universal constants γ₀ > 0 and
R ∈ (0, 1/16) such that, whenever d_tr(ρ, |0⟩⟨0|) ≤ γ₀, the infidelity objective satisfies
I ⪯ ∇²f_ρ(θ) ⪯ 3I (θ ∈ B_R), (24) and its unique minimizer θ_∗ over B_R satisfies ‖θ_∗‖_P ≤ R/4."

**Formalization Note.** `B_r = {θ ∈ P : ‖θ‖_P ≤ r}` (p. 19) is `Metric.closedBall 0 r` in `Pspace n`,
whose norm is `‖·‖_P`. `∇²f_ρ(θ)` is the derivative of the gradient, a linear map on `Pspace n`;
its operator norm is the one induced by `‖·‖_P`; `I ⪯ H ⪯ 3I` is `‖h‖² ≤ ⟨h, Hh⟩ ≤ 3‖h‖²` for all `h`.
The second part asserts that a minimizer of `f_ρ` over `B_R` exists, is unique, and has norm at most
`R/4`. All constants are universal (before `n` and `ρ`). -/
theorem proposition_3_9 :
    (∃ r₀ : ℝ, 0 < r₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (ρ : State (Occupation (Fin n))) (θ : Pspace n), ‖θ‖ ≤ r₀ →
        ‖fderiv ℝ (gradient (fobj ρ.coefficients)) θ - (2 : ℝ) • ContinuousLinearMap.id ℝ (Pspace n)‖ ≤
          C * (‖θ‖ + (BosonicLearn.traceDist ρ.coefficients (vacuum n)).toReal)) ∧
    (∃ γ₀ : ℝ, 0 < γ₀ ∧ ∃ R : ℝ, 0 < R ∧ R < 1 / 16 ∧
      ∀ (n : ℕ) (ρ : State (Occupation (Fin n))),
        BosonicLearn.traceDist ρ.coefficients (vacuum n) ≤ ENNReal.ofReal γ₀ →
        (∀ θ : Pspace n, ‖θ‖ ≤ R → ∀ h : Pspace n,
          ‖h‖ ^ 2 ≤ inner ℝ h (fderiv ℝ (gradient (fobj ρ.coefficients)) θ h) ∧
          inner ℝ h (fderiv ℝ (gradient (fobj ρ.coefficients)) θ h) ≤ 3 * ‖h‖ ^ 2) ∧
        ∃ θs ∈ Metric.closedBall (0 : Pspace n) R,
          IsMinOn (fobj ρ.coefficients) (Metric.closedBall 0 R) θs ∧
          (∀ θ' ∈ Metric.closedBall (0 : Pspace n) R,
            IsMinOn (fobj ρ.coefficients) (Metric.closedBall 0 R) θ' → θ' = θs) ∧
          ‖θs‖ ≤ R / 4) := by sorry

end AgnGaussTomo
