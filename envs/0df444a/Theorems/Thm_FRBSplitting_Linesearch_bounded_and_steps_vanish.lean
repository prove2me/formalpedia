-- Prove2me | Theorems.Thm_FRBSplitting_Linesearch_bounded_and_steps_vanish
-- name    : FRBSplitting.Linesearch.bounded_and_steps_vanish
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:50.663548+00:00
-- url     : https://prove2.me/theorems/c95611fd-e4b3-4a43-95c9-b7259ddbe2c5
-- title:
--   Proof of Theorem 3.4, p. 11 — the linesearch iterates are bounded and ‖x_k − x_{k+1}‖ → 0
-- statement:
--   Let $H$ be a real inner product space, $A:H\rightrightarrows H$ maximally monotone with resolvents $J_{tA}$, and $B:H\to H$ monotone and locally Lipschitz, with $(A+B)^{-1}(0)\neq\emptyset$. Let $\delta,\sigma\in(0,1)$ and let $(x_k)_{k\ge-1}$, $(\lambda_k)_{k\ge-1}$ be a run of Algorithm 1 with $\lambda_{-1}>0$. Then $(x_k)$ is bounded and
--   $$\lim_{k\to\infty}\|x_k-x_{k+1}\|=0.$$
--
--   This is the first step of the proof of Theorem 3.4, obtained from Lemma 3.3 by telescoping, as in the proof of Theorem 2.5.
--
--   **Formalization Note.** Finite dimensionality of $H$ is not needed for this step and is dropped (a stronger statement); local Lipschitz continuity is kept from the theorem's hypotheses although this step uses only (30). Indices are shifted (`x j` $=x_{j-1}$); boundedness is `Bornology.IsBounded (Set.range x)`.
-- source:
--   Malitsky & Tam, A Forward-Backward Splitting Method for Monotone Inclusions Without Cocoercivity, arXiv:1808.04162v4, p. 11, proof of Theorem 3.4, first paragraph

import Mathlib
import Definitions.Def_ThreeOpSplitting_Accel_MonotoneOperators
import Definitions.Def_FRBSplitting_Linesearch_Setting
open InnerProductSpace ThreeOpSplitting.Accel

namespace FRBSplitting.Linesearch

theorem bounded_and_steps_vanish {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → Set H) (B : H → H) (J : ℝ → H → H) (δ σ : ℝ)
    (hA : IsMaximalMonotone A)
    (hJ : IsResolventFamily A J)
    (hBm : IsMonotoneFun B) (hBloc : LocallyLipschitz B)
    (hzer : (FRBSplitting.Weak.zeroSet A B).Nonempty)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (lam : ℕ → ℝ) (x : ℕ → H) (hlam0 : 0 < lam 0) (hrun : IsLinesearchRun J B δ σ lam x) :
    Bornology.IsBounded (Set.range x) ∧
      Filter.Tendsto (fun k => ‖x k - x (k + 1)‖) Filter.atTop (nhds 0) := by sorry

end FRBSplitting.Linesearch
