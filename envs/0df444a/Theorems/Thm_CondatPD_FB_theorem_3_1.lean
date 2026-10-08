-- Prove2me | Theorems.Thm_CondatPD_FB_theorem_3_1
-- name    : CondatPD.FB.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:56:59.374989+00:00
-- url     : https://prove2.me/theorems/0af16f42-d4f6-41f5-a0ac-9e2f9d1d5e1a
-- title:
--   Theorem 3.1 — weak convergence of Algorithms 3.1 and 3.2
-- statement:
--   Let $F:\mathcal X\to\mathbb R$ be convex with $\beta$-Lipschitz gradient for $\beta>0$, let $G\in\Gamma_0(\mathcal X)$ and $H\in\Gamma_0(\mathcal Y)$, and let $L:\mathcal X\to\mathcal Y$ be bounded linear. Assume the primal–dual inclusion (6) has a solution. Choose $\tau,\sigma>0$, put $\delta=2-(\beta/2)(1/\tau-\sigma\|L\|^2)^{-1}$, and suppose
--   $$(i)\quad 1/\tau-\sigma\|L\|^2\ge\beta/2,\qquad (ii)\quad0<\rho_n<\delta\ \text{for every }n,$$
--   $$(iii)\quad\sum_{n\ge0}\rho_n(\delta-\rho_n)=+\infty,\qquad (iv)\quad\sum_{n\ge0}\rho_n\|e_{F,n}\|,\ \sum_{n\ge0}\rho_n\|e_{G,n}\|,\ \sum_{n\ge0}\rho_n\|e_{H,n}\|<+\infty.$$
--   For every run of Algorithm 3.1 and every run of Algorithm 3.2, both the primal and dual iterates converge weakly to the components of a solution of (6). The limit pair may depend on the run.
--
--   This is the paper's principal convergence theorem in the positive smoothness regime.
--
--   **Formalization Note** The algorithm runs explicitly include all errors. Proximity maps are given by their published minimizer predicate; for the stated proper closed convex functions and positive step sizes, such maps exist uniquely. The nonempty solution set is the standing assumption on p. 4 and also implies the paper's earlier nonempty primal-minimizer assumption. Divergence is expressed through finite partial sums tending to $+\infty$.
-- source:
--   Condat, A primal–dual splitting method for convex optimization involving Lipschitzian, proximable and linear composite terms, J. Optim. Theory Appl. 158(2) (2013), final author's version (HAL hal-00609728v5), p. 5, Theorem 3.1; standing assumptions pp. 3–4

import Mathlib
import Definitions.Def_CondatPD_FB_Setting
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence

open Filter Topology InnerProductSpace

namespace CondatPD.FB

/-- Theorem 3.1, p. 5: both algorithms converge weakly under (i)–(iv). -/
theorem theorem_3_1 {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [CompleteSpace Y]
    (F : X → ℝ) (G : X → EReal) (H : Y → EReal) (L : X →L[ℝ] Y)
    (β τ σ : ℝ) (PG : X → X) (PH : Y → Y)
    (ρ : ℕ → ℝ) (eF eG : ℕ → X) (eH : ℕ → Y)
    (hF : IsSmoothTerm β F)
    (hG : ThreeOpSplitting.ConvexRates.IsProperClosedConvex G)
    (hH : ThreeOpSplitting.ConvexRates.IsProperClosedConvex H)
    (hsol : ∃ xh yh, IsPDSolution F G H L xh yh)
    (hβ : 0 < β) (hτ : 0 < τ) (hσ : 0 < σ)
    (hPG : ThreeOpSplitting.ConvexRates.IsProx τ G PG)
    (hPH : ThreeOpSplitting.ConvexRates.IsProx σ (conj H) PH)
    (hi : β / 2 ≤ 1 / τ - σ * ‖L‖ ^ 2)
    (hii : ∀ n, 0 < ρ n ∧ ρ n < pdDelta β τ σ L)
    (hiii : Tendsto (fun N => ∑ n ∈ Finset.range N,
      ρ n * (pdDelta β τ σ L - ρ n)) atTop atTop)
    (hivF : Summable (fun n => ρ n * ‖eF n‖))
    (hivG : Summable (fun n => ρ n * ‖eG n‖))
    (hivH : Summable (fun n => ρ n * ‖eH n‖)) :
    (∀ (x : ℕ → X) (y : ℕ → Y),
      IsAlg31Run F L PG PH τ σ ρ eF eG eH x y →
        ∃ xh yh, IsPDSolution F G H L xh yh ∧
          ThreeOpSplitting.Convergence.WeakTendsto x xh ∧
          ThreeOpSplitting.Convergence.WeakTendsto y yh) ∧
    (∀ (x : ℕ → X) (y : ℕ → Y),
      IsAlg32Run F L PG PH τ σ ρ eF eG eH x y →
        ∃ xh yh, IsPDSolution F G H L xh yh ∧
          ThreeOpSplitting.Convergence.WeakTendsto x xh ∧
          ThreeOpSplitting.Convergence.WeakTendsto y yh) := by sorry

end CondatPD.FB
