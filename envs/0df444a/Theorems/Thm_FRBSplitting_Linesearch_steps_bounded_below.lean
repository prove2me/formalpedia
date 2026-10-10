-- Prove2me | Theorems.Thm_FRBSplitting_Linesearch_steps_bounded_below
-- name    : FRBSplitting.Linesearch.steps_bounded_below
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:43:51.514779+00:00
-- url     : https://prove2.me/theorems/d0c66a85-d18b-453c-af1e-7de850f51471
-- title:
--   Proof of Theorem 3.4, p. 11 — the linesearch step sizes (λ_k) are bounded away from zero
-- statement:
--   Let $H$ be a finite-dimensional real inner product space, $A:H\rightrightarrows H$ maximally monotone with resolvents $J_{tA}$, and $B:H\to H$ monotone and locally Lipschitz, with $(A+B)^{-1}(0)\neq\emptyset$. Let $\delta,\sigma\in(0,1)$ and let $(x_k)_{k\ge-1}$, $(\lambda_k)_{k\ge-1}$ be a run of Algorithm 1 with $\lambda_{-1}>0$. Then there is $c>0$ with
--   $$\lambda_k\ge c\qquad\text{for all }k\ge-1.$$
--
--   With the step sizes bounded below, the remainder of the proof of Theorem 3.4 follows that of Theorem 2.5.
--
--   **Formalization Note.** The bound covers every index of the shifted sequence `lam j` $=\lambda_{j-1}$, $j\ge0$, including $\lambda_{-1}$. The page derives the claim "by combining (30) and (33)"; since (33) concerns accepted iterates, the argument also needs the rejected trial points to stay in a bounded set, which holds — the statement is the page's.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 11, proof of Theorem 3.4, last paragraph

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Linesearch_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Linesearch

theorem steps_bounded_below {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (δ σ : ℝ)
    (hA : IsMaximalMonotone A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B) (hBloc : LocallyLipschitz B)
    (hzer : (FRBSplitting.Weak.zeroSet A B).Nonempty)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (lam : ℕ → ℝ) (x : ℕ → H) (hlam0 : 0 < lam 0) (hrun : IsLinesearchRun J B δ σ lam x) :
    ∃ c : ℝ, 0 < c ∧ ∀ j : ℕ, c ≤ lam j := by sorry

end FRBSplitting.Linesearch
