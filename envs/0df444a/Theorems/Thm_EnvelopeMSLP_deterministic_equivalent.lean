-- Prove2me | Theorems.Thm_EnvelopeMSLP_deterministic_equivalent
-- name    : EnvelopeMSLP.deterministic_equivalent
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:29:19.792199+00:00
-- url     : https://prove2.me/theorems/e881b711-d82d-46f6-b05d-c1a8c9c43c1c
-- title:
--   §3.1, p.14 — (7) is one linear program of form (6), with primal and dual bijections
-- statement:
--   There are data $A(\theta),b(\theta),c(\theta)$ of form (6), each entry a fixed real polynomial in the joint data of (7), a bijection $\varphi$ from LP vectors to nonanticipative policies and a bijection $\psi$ from LP dual vectors to nonanticipative multipliers, both independent of $\theta$, such that at every $\theta$:
--
--   1. $y$ is feasible for (6) if and only if $\varphi(y)$ is feasible for (7), and the objectives agree;
--   2. $\mu$ is dual feasible for (6) if and only if $\psi(\mu)$ is a dual feasible multiplier, and the dual objectives agree;
--   3. wherever the joint data are differentiable, the envelope expression of the LP at $(y,\mu)$ equals the right-hand side of (9) at $(\varphi(y),\psi(\mu))$.
--
--   The construction has one variable block and one constraint block per node of the history tree, the objective of a node is scaled by its probability, and the dual variable at a node is the node's probability times $\lambda$ at that node. The statement makes the sentence of the paper precise: when the problem is solved as one monolithic linear program, all primal and dual solutions are known and (9) can be evaluated.
--
--   Differences from the source:
--   - reading: solved as one large monolithic linear program, via a deterministic equivalent formulation → existence of LP data polynomial in the joint data, with primal and dual bijections preserving feasibility, objectives and the envelope expression; reason: this is what the sentence on p.14 needs to be true of (9)
--   - encoding: a discrete process ξ on a probability space (Ω, F, P) → a finite scenario type Ω with p(ω) > 0 summing to 1; reason: this is the support of the law of ξ (p.12: finitely many atoms); a general space pushes forward onto it and the statement sees only the law
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), §3.1, p.14

import Mathlib
import Definitions.Def_EnvelopeMSLP_FreeFeasible
import Definitions.Def_EnvelopeMSLP_FreeDualFeasible
import Definitions.Def_EnvelopeMSLP_MSLP_IsFeasible
import Definitions.Def_EnvelopeMSLP_MSLP_objective
import Definitions.Def_EnvelopeMSLP_MSLP_IsDualFeasible
import Definitions.Def_EnvelopeMSLP_MSLP_dualObjective
import Definitions.Def_EnvelopeMSLP_MSLP_envelopeRHS
import Definitions.Def_EnvelopeMSLP_MSLP_mslpData
open Matrix

namespace EnvelopeMSLP

/-- **The deterministic equivalent.** Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), §3.1, p.14: (7) is "one large monolithic linear program" of
form (6), and "all primal and dual solutions for all possible scenarios are known and (9) can be easily
evaluated". There are data `A(θ), b(θ), c(θ)` of form (6), each entry a fixed real polynomial in the joint
data `mslpData θ`, a bijection `φ` from LP vectors to nonanticipative policies and a bijection `ψ` from
LP dual vectors to nonanticipative multipliers, neither depending on `θ`, such that at every `θ`:
1. `φ` preserves feasibility and the objective;
2. `ψ` preserves dual feasibility and the objective;
3. where the joint data are differentiable, the envelope expression of the LP at `(y, μ)` is the
   right-hand side of (9) at `(φ y, ψ μ)`.

**Formalization Note.** In the construction there is one variable block and one constraint block per node
of the history tree, the objective of a node is scaled by its probability, and the LP dual variable at a
node is `P(node)` times `λ` at that node. -/
theorem deterministic_equivalent {T : ℕ} {Ω : Type*} [Fintype Ω] (P : MSLP T Ω) :
    ∃ (r s : ℕ) (A : ℝ → Matrix (Fin r) (Fin s) ℝ) (b : ℝ → Fin r → ℝ) (c : ℝ → Fin s → ℝ)
      (pA : Fin r → Fin s → MvPolynomial P.DataIndex ℝ) (pb : Fin r → MvPolynomial P.DataIndex ℝ)
      (pc : Fin s → MvPolynomial P.DataIndex ℝ)
      (φ : (Fin s → ℝ) ≃ {x : P.Policy // P.IsNonanticipative x})
      (ψ : (Fin r → ℝ) ≃ {lam : P.Multiplier // P.IsNonanticipativeMultiplier lam}),
      (∀ θ i j, A θ i j = MvPolynomial.eval (P.mslpData θ) (pA i j)) ∧
      (∀ θ i, b θ i = MvPolynomial.eval (P.mslpData θ) (pb i)) ∧
      (∀ θ j, c θ j = MvPolynomial.eval (P.mslpData θ) (pc j)) ∧
      (∀ θ y, FreeFeasible (A θ) (b θ) y ↔ P.IsFeasible θ (φ y).1) ∧
      (∀ θ y, c θ ⬝ᵥ y = P.objective θ (φ y).1) ∧
      (∀ θ μ, FreeDualFeasible (A θ) (c θ) μ ↔ P.IsDualFeasible θ (ψ μ).1) ∧
      (∀ θ μ, b θ ⬝ᵥ μ = P.dualObjective θ (ψ μ).1) ∧
      ∀ θ, (∀ k, DifferentiableAt ℝ (fun θ' => P.mslpData θ' k) θ) → ∀ y μ,
        deriv c θ ⬝ᵥ y + μ ⬝ᵥ (deriv b θ - matDeriv A θ *ᵥ y) =
          P.envelopeRHS θ (φ y).1 (ψ μ).1 := by sorry

end EnvelopeMSLP
