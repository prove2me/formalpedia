-- Prove2me | Theorems.Thm_ContinualHardness_Linear_lemma_A_4
-- name    : ContinualHardness.Linear.lemma_A_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:12:43.518727+00:00
-- url     : https://prove2.me/theorems/b33a4b7d-4e7a-489f-83e6-739fe856a20a
-- title:
--   Lemma A.4 — every task of the dictatorship test is perfectly separated by a weight vector supported on its block with positive block sum
-- statement:
--   Let $\varepsilon>0$, $T,M\ge1$ with $\varepsilon\le T$, a scale $\sigma>0$, and let $\tilde D_1,\dots,\tilde D_T$ be the datasets of the dictatorship test $\mathrm{Dict}$ (§A.2). Fix $t\in[T]$ and $r\in\mathbb R^{[T]\times[M]}$ with (i) $r_{t'j}=0$ for every $t'\ne t$ and every $j$, and (ii) $\sum_{j\in[M]}r_{tj}>0$. Then the homogeneous linear classifier $h(x)=\operatorname{sign}(r^{\mathsf T}x)$ classifies $\tilde D_t$ perfectly:
--   $$\mathrm{Acc}(\tilde D_t,h)=1 .$$
--   This is the per-task tractability of the test; in the reduction it gives the separability of every final dataset.
--
--   Differences from the source:
--   - generalization: the test's scale σ = (1/δ)√(8TM/(πε)) of (7) → every scale σ > 0; reason: the statement does not depend on σ's value; the σ of (7) is positive, so the lemma specializes to it
--   - encoding: Dict(ε, δ, T, M) for ε > 0 → hypothesis ε ≤ T (with ε > 0); reason: the coordinate probabilities ε/T and 1 − ε/T lie in [0, 1] only then; it excludes only parameters for which the test is undefined
--   - encoding: D̃_t is linearly separable using h → Acc(D̃_t, sign(rᵀx)) = 1, with D̃_t the finitely supported law of the sampling procedure on ℝ^{[T]×[M]} (coordinates Fin T × Fin M); reason: Lean representation of the dataset and of 'separable using h'
-- source:
--   Saket, Intractability of Continual Learning using Parametric Models with Unlimited Replay Buffer, STOC 2027 submission (manuscript sha256 86821df1…), p. 17, Lemma A.4 (PDF p. 18)

import Mathlib
import Definitions.Def_ContinualHardness_Linear_Dataset
import Definitions.Def_ContinualHardness_Linear_Dict

namespace ContinualHardness.Linear

/-- Lemma A.4 (Linear separability of every `D̃_t`), p. 17. For every block `t`, every
homogeneous linear classifier `sign(rᵀx)` whose weight vector vanishes outside block `t` and has
positive block sum `∑_j r_{tj} > 0` has accuracy `1` on `D̃_t`. -/
theorem lemma_A_4 (ε σ : ℝ) (T M : ℕ) (hε : 0 < ε) (hεT : ε ≤ T) (hσ : 0 < σ)
    (t : Fin T) (r : Fin T × Fin M → ℝ)
    (hoff : ∀ t' : Fin T, t' ≠ t → ∀ j : Fin M, r (t', j) = 0)
    (hpos : 0 < ∑ j : Fin M, r (t, j)) :
    acc (dictData ε σ T M t) (linClf r 0) = 1 := by sorry

end ContinualHardness.Linear
