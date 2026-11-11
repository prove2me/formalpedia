-- Prove2me | Theorems.Thm_ContinualHardness_Linear_lemma_A_6
-- name    : ContinualHardness.Linear.lemma_A_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:12:43.843682+00:00
-- url     : https://prove2.me/theorems/f6323635-8511-4a65-abcc-8dba20a0f427
-- title:
--   Lemma A.6 — accuracy different from 1/2 on a task forces a nonzero block sum
-- statement:
--   Let $\varepsilon>0$, $T,M\ge1$ with $\varepsilon\le T$, a scale $\sigma>0$, and let $\tilde D_1,\dots,\tilde D_T$ be the datasets of the dictatorship test (§A.2). Fix a linear classifier $h(x)=\operatorname{sign}(r^{\mathsf T}x+c)$ with arbitrary $r\in\mathbb R^{[T]\times[M]}$ and $c\in\mathbb R$ (recall $\operatorname{sign}(0)=-1$). For every $t\in[T]$:
--   $$\mathrm{Acc}(\tilde D_t,h)\ne\tfrac12\ \Longrightarrow\ \sum_{j\in[M]}r_{tj}\ne0 .$$
--   This non-degeneracy property is used in the NO case to show that the block sums $a_t$, $a_s$ are nonzero.
--
--   Differences from the source:
--   - generalization: the test's scale σ = (1/δ)√(8TM/(πε)) of (7) → every scale σ > 0; reason: the statement does not depend on σ's value; the σ of (7) is positive, so the lemma specializes to it
--   - encoding: Dict(ε, δ, T, M) for ε > 0 → hypothesis ε ≤ T (with ε > 0); reason: the coordinate probabilities lie in [0, 1] only then; it excludes only parameters for which the test is undefined
-- source:
--   Saket, Intractability of Continual Learning using Parametric Models with Unlimited Replay Buffer, STOC 2027 submission (manuscript sha256 86821df1…), p. 18, Lemma A.6 (PDF p. 19)

import Mathlib
import Definitions.Def_ContinualHardness_Linear_Dataset
import Definitions.Def_ContinualHardness_Linear_Dict

namespace ContinualHardness.Linear

/-- Lemma A.6, p. 18. For a linear classifier `h(x) = sign(rᵀx + c)` and a block `t`: if
`Acc(D̃_t, h) ≠ 1/2` then `∑_j r_{tj} ≠ 0`. -/
theorem lemma_A_6 (ε σ : ℝ) (T M : ℕ) (hε : 0 < ε) (hεT : ε ≤ T) (hσ : 0 < σ)
    (r : Fin T × Fin M → ℝ) (c : ℝ) (t : Fin T)
    (hacc : acc (dictData ε σ T M t) (linClf r c) ≠ 1 / 2) :
    ∑ j : Fin M, r (t, j) ≠ 0 := by sorry

end ContinualHardness.Linear
