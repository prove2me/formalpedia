-- Prove2me | Theorems.Thm_EnvelopeMSLP_theorem_3
-- name    : EnvelopeMSLP.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:31:58.2857+00:00
-- url     : https://prove2.me/theorems/288b057a-8a09-4ba6-a01e-7eaaeefcd800
-- title:
--   Theorem 3 (corrected: tame data, joint multipliers) — the optimal value of an MSLP is almost everywhere differentiable, with the envelope formula (9)
-- statement:
--   Let $\Theta\subseteq\mathbb R$ be open, and consider a finitely supported multi-stage linear program (7) with optimal value $V(\theta)$ whose data are differentiable and tame on $\Theta$. Then for Lebesgue-almost every $\theta\in\Theta$ at which (7) has a solution:
--
--   1. (7) has a solution at every $\theta'$ near $\theta$;
--   2. an optimal joint multiplier exists at $\theta$;
--   3. $V$ has a derivative at $\theta$;
--   4. for every optimal policy $x^*$ and every optimal joint multiplier $\lambda^*$ at $\theta$,
--   $$V'(\theta)=\mathbb E\Big[\sum_{t=1}^T\langle\nabla c_t(\theta),x^*_t\rangle+\Big\langle\lambda^*_t,\nabla h_t(\theta)-\tfrac{d}{d\theta}T_t(\theta)x^*_{t-1}-\tfrac{d}{d\theta}W_t(\theta)x^*_t\Big\rangle\Big].$$
--
--   So the derivative of the optimal value of a multi-stage stochastic linear program can be read off one optimal primal-dual solution, without re-solving the problem.
--
--   **Formalization Note** The null set does not depend on the pair $(x^*,\lambda^*)$. Tameness is a condition on the data alone, and real-analytic data satisfy it.
--
--   Differences from the source:
--   - correction: Dt differentiable, invertible and bi-continuous → differentiable on Θ and IsTameData on Θ; reason: counterexample (T = 1, ξ₁ constant, p.7 example (3) with θ replaced by a C∞ map): Θ = (0,1), K ⊂ Θ a fat Cantor set, h C∞ with h⁻¹(0) = K, p = 1 − h, V(θ) = max ½p(θ)x + y s.t. x + y ≤ 1, −x − p(θ)y ≤ −1, −x ≤ 0, −y ≤ 0, 0 ≤ 2 + θ; the data are C∞, injective and bi-continuous, the problem is solvable at every θ, and V = 1 on K while V = p/2 < ½ off K, so V is discontinuous on a set of positive measure
--   - reading: λ*_t are the optimal dual solutions associated with the constraints in stage t → optimal joint multipliers, the dual of the deterministic equivalent normalised by node probability; reason: with stage-LP duals (9) is false: T = 2, one scenario, x₁ ∈ ℝ, c₁ = 0, stage 2 max y s.t. y − x₁ ≤ 0, y + x₁ ≤ 2θ has V(θ) = θ, x₁* = θ, every (λ₁, λ₂) ≥ 0 with λ₁ + λ₂ = 1 optimal for the stage LP, and (9) gives 2λ₂, so λ = (1,0) gives 0 ≠ 1; p.14 points to the monolithic LP
--   - generalization: invertible and bi-continuous data, for every α ∈ R^Mt → no invertibility, data conditions at the atoms ξ_t(ω) only; reason: the proof uses neither; data satisfying the source's conditions and tameness are covered
--   - reading: xt(θ, ξt) as printed in (7) → xt a function of the history ξ^t; reason: (8) conditions on ξ^t and §3.2, p.16, says the whole history may be required
--   - reading: if for θ the problem has a solution, the derivative can be written as (9) for almost all θ → for a.e. θ: solvable at θ implies nearby solvability, existence of a multiplier and V′, and (9) for every optimal pair; reason: Θ need not be solvable throughout; the existence clauses keep the derivative and the quantifier over λ* from being empty
--   - encoding: a discrete process ξ on a probability space (Ω, F, P) → a finite scenario type Ω with p(ω) > 0 summing to 1; reason: this is the support of the law of ξ (p.12: finitely many atoms); a general space pushes forward onto it and the statement sees only the law
--   - encoding: V(θ) real valued → the EReal value read through toReal; reason: by clause 1 the value is finite near θ
--   - encoding: Dt : Θ × R^Mt → R^Nt, stages t = 1, …, T, x0 given → data W, T, c, h defined for every θ ∈ ℝ, stages t : Fin T (Lean stage t is the paper's t + 1), x0 a field of the program; reason: every hypothesis and conclusion looks only at θ in the open set Θ or near such θ, so values off Θ are never used; the index shift changes no instance
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), Theorem 3, display (9), p.13

import Mathlib
import Definitions.Def_EnvelopeMSLP_MSLP_Solvable
import Definitions.Def_EnvelopeMSLP_MSLP_value
import Definitions.Def_EnvelopeMSLP_MSLP_IsOptimalMultiplier
import Definitions.Def_EnvelopeMSLP_MSLP_envelopeRHS
import Definitions.Def_EnvelopeMSLP_MSLP_mslpData
import Definitions.Def_EnvelopeMSLP_IsTameData
open MeasureTheory Topology Filter

namespace EnvelopeMSLP

/-- **Theorem 3 (corrected): the envelope theorem for multi-stage linear programs.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), Theorem 3,
display (9), p.13, which is false as printed. Let `Θ ⊆ ℝ` be open, and let the data of the finitely supported
program (7) be differentiable on `Θ` and tame on `Θ`. Then for Lebesgue-almost every `θ ∈ Θ` at which (7) has
a solution:
1. (7) has a solution at every `θ′` near `θ`;
2. an optimal joint multiplier exists at `θ`;
3. `V` has a derivative `V′` at `θ`;
4. `V′` equals the right-hand side of (9) for **every** optimal policy `x*` and **every** optimal joint
   multiplier `λ*` at `θ`.

**Formalization Note.** `V` is `P.value` read in `ℝ`, the true value near `θ` by clause 1. The null set does
not depend on `x*` or `λ*`. The tameness hypothesis is about the data alone. -/
theorem theorem_3 {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) (Θ : Set ℝ) (hΘ : IsOpen Θ)
    (hdiff : ∀ k, DifferentiableOn ℝ (fun θ => P.mslpData θ k) Θ)
    (htame : IsTameData Θ P.mslpData) :
    ∀ᵐ θ ∂(volume.restrict Θ), P.Solvable θ →
      (∀ᶠ θ' in 𝓝 θ, P.Solvable θ') ∧
      (∃ lam, P.IsOptimalMultiplier θ lam) ∧
      ∃ V', HasDerivAt (fun θ' => (P.value θ').toReal) V' θ ∧
        ∀ x lam, P.IsOptimalPolicy θ x → P.IsOptimalMultiplier θ lam →
          V' = P.envelopeRHS θ x lam := by sorry

end EnvelopeMSLP
