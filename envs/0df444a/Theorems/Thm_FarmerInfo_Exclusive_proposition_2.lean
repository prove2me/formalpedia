-- Prove2me | Theorems.Thm_FarmerInfo_Exclusive_proposition_2
-- name    : FarmerInfo.Exclusive.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:15:04.24699+00:00
-- url     : https://prove2.me/theorems/6ad3ded3-1ffc-4cf9-b486-06331c4e3a08
-- title:
--   Proposition 2, p. 14 — one recipient if V > 0, none if V ≤ 0
-- statement:
--   Let $n\geq4$ farmers face a linear inverse demand curve with a centered Gaussian intercept shock of precision $\alpha>0$. Each farmer has an independent private signal noise of precision $\gamma>0$, and those selected by the planner also observe a common public signal whose noise has precision $\beta>0$. Demand sensitivity $b$ and market potential $a$ are positive. Production quantities are real valued.
--
--   For every informed set there is an admissible Bayesian Nash equilibrium. When the threshold polynomial $V(n,\beta;\gamma)$ is positive, every one-farmer informed set has strictly greater total equilibrium profit than any set of a different size. When $V\leq0$, informing no farmer is optimal; when $V<0$, it is strictly better than every nonempty informed set:
--
--   $$n_1^*=1\quad(V>0),\qquad n_1^*=0\quad(V\leq0).$$
--
--   The result specifies the welfare-maximizing access policy across all subsets of farmers.
--
--   **Formalization Note** At $V=0$, zero and one recipient tie, so the second branch is non-strict. Strategies are real valued, measurable and square-integrable; the game is the unconstrained interpretation of the paper’s affine equilibrium. Positive $\alpha,\beta,\gamma$ and $n\geq4$ are assumed.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (version of June 27, 2019), p. 14, Proposition 2; p. 36, Proof of Proposition 2

import Mathlib
import Definitions.Def_FarmerInfo_Exclusive_Setting

namespace FarmerInfo.Exclusive

open MeasureTheory Finset

noncomputable section

/-- Proposition 2, p. 14: a single recipient wins for V > 0, and none wins for V ≤ 0. -/
theorem proposition_2 (M : Model) (hM : M.Standing) :
    (∀ I : Finset (Fin M.n), ∃ σ : Fin M.n → Model.Strategy, M.IsBNE I σ) ∧
    (0 < M.V → ∀ I I' : Finset (Fin M.n), I'.card = 1 → I.card ≠ 1 →
      ∀ σ σ' : Fin M.n → Model.Strategy,
        M.IsBNE I σ → M.IsBNE I' σ' → M.welfare I σ < M.welfare I' σ') ∧
    (M.V ≤ 0 → ∀ I : Finset (Fin M.n),
      ∀ σ σ' : Fin M.n → Model.Strategy,
        M.IsBNE I σ → M.IsBNE ∅ σ' → M.welfare I σ ≤ M.welfare ∅ σ') ∧
    (M.V < 0 → ∀ I : Finset (Fin M.n), I.Nonempty →
      ∀ σ σ' : Fin M.n → Model.Strategy,
        M.IsBNE I σ → M.IsBNE ∅ σ' → M.welfare I σ < M.welfare ∅ σ') := by sorry
end
end FarmerInfo.Exclusive
