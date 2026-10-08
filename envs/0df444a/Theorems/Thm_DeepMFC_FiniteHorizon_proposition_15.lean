-- Prove2me | Theorems.Thm_DeepMFC_FiniteHorizon_proposition_15
-- name    : DeepMFC.FiniteHorizon.proposition_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:57.145039+00:00
-- url     : https://prove2.me/theorems/610b21ac-332d-4443-9316-c2f9faa9237c
-- title:
--   Proposition 15, p. 4078 — for a regular Lipschitz feedback φ, |J^N(φ) − J̌^N(φ)| ≤ C√Δt, uniformly in N
-- statement:
--   Assume (A1)–(A4), (B1), (B3), (C1). For all $L,M,C_1\ge0$ there is a constant $C$ with the following property. Let $\varphi$ be a feedback that is $L$-Lipschitz in $(t,x)$ on $[0,T]\times\mathbb R^d$ with $|\varphi(0,0)|\le M$, differentiable in $t$ and twice differentiable in $x$, such that for every $(t,x)\in[0,T]\times\mathbb R^d$,
--   $$|\partial_t\varphi(t,x)|\le C_1\big(1+|(t,x)|\big),\qquad|\partial_x\varphi(t,x)|\le C_1,\qquad|\partial^2_{xx}\varphi(t,x)|\le C_1.\qquad(3.16)$$
--   Then for all $N\ge1$ and $N_T\ge1$, with $\Delta t=T/N_T$,
--   $$|J^N(\varphi)-\check J^N(\varphi)|\le C\sqrt{\Delta t}.$$
--
--   This is the third step of Theorem 3: discretizing time with the Euler scheme changes the $N$-agent cost of a regular feedback by $O(\sqrt{\Delta t})$, uniformly in the number of agents.
--
--   **Formalization Note.** The page's first bound in (3.16) reads $|\partial_t\varphi(t,x)|\le C_1|(t,x)|$, which forces $\partial_t\varphi(0,0)=0$ and is not satisfied by the networks to which the paper applies the proposition; its proof uses the bound only through quadratic-growth estimates. The statement here takes the corrected reading $C_1(1+|(t,x)|)$, a weaker hypothesis. The derivatives are witnesses: $\partial_t\varphi$ a derivative within $[0,T]$, $\partial_x\varphi$, $\partial^2_{xx}\varphi$ Fréchet derivatives in $x$ (operator norms). $J^N(\varphi)$ is computed on any Problem-3 space and any solution of (3.2); $\check J^N(\varphi)$ is the law-level cost (2.12). The page's "for all $N$ and $t\in[0,T]$" is read as all $N\ge1$ and all mesh sizes $\Delta t=T/N_T$.
-- source:
--   Carmona, Laurière, Convergence analysis of machine learning algorithms for the numerical solution of mean field control and games: II—the finite horizon case, Ann. Appl. Probab. 32(6) (2022), https://doi.org/10.1214/21-AAP1715, p. 4078, Proposition 15, (3.16)

import Mathlib
import Definitions.Def_DeepMFC_FiniteHorizon_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DeepMFC.FiniteHorizon

theorem proposition_15 {d k : ℕ} (M : Model d k) (D : Deriv d k) (hC : Coeff M D) :
    ∀ L Mφ C₁ : ℝ, ∃ C : ℝ,
      ∀ φ : ℝ → E d → Fin k → ℝ, FeedbackLip M L φ → ‖φ 0 0‖ ≤ Mφ →
      ∀ (φt : ℝ → E d → Fin k → ℝ) (φx : ℝ → E d → E d →L[ℝ] (Fin k → ℝ))
        (φxx : ℝ → E d → E d →L[ℝ] E d →L[ℝ] (Fin k → ℝ)),
        (∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ x : E d,
          HasDerivWithinAt (fun s => φ s x) (φt t x) (Set.Icc (0 : ℝ) M.T) t ∧
          HasFDerivAt (φ t) (φx t x) x ∧ HasFDerivAt (φx t) (φxx t x) x ∧
          ‖φt t x‖ ≤ C₁ * (1 + ‖(t, x)‖) ∧ ‖φx t x‖ ≤ C₁ ∧ ‖φxx t x‖ ≤ C₁) →
      ∀ N NT : ℕ, 1 ≤ N → 1 ≤ NT →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (W : Fin N → ℝ≥0 → Ω → E d)
        (X0 : Fin N → Ω → E d), Setting3 M P W X0 →
      ∀ X : Fin N → ℝ≥0 → Ω → E d, Solves32 M P W X0 φ X →
        |JN M P φ X - Jcheck M N NT φ| ≤ C * Real.sqrt ((M.T : ℝ) / NT) := by sorry

end DeepMFC.FiniteHorizon
