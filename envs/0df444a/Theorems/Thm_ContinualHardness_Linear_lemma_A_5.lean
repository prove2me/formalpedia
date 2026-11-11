-- Prove2me | Theorems.Thm_ContinualHardness_Linear_lemma_A_5
-- name    : ContinualHardness.Linear.lemma_A_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:12:57.745714+00:00
-- url     : https://prove2.me/theorems/90b21bfa-bca7-4fdb-a48e-2dfcf067bd26
-- title:
--   Lemma A.5 — the dictator classifier sign(Σ_t x_{tj*}) has accuracy at least 1 − ε on every task
-- statement:
--   Let $\varepsilon>0$, $T,M\ge1$ with $\varepsilon\le T$, a scale $\sigma>0$, and let $\tilde D_1,\dots,\tilde D_T$ be the datasets of the dictatorship test (§A.2). For every coordinate $j^*\in[M]$ and every task $t\in[T]$, the dictator classifier $h_{j^*}(x)=\operatorname{sign}\big(\sum_{t'\in[T]}x_{t'j^*}\big)$ satisfies
--   $$\mathrm{Acc}(\tilde D_t,h_{j^*})\ \ge\ 1-\varepsilon .$$
--   This is the completeness of the test: one homogeneous linear classifier is good on all tasks at once. It gives the YES case of Theorem A.8.
--
--   Differences from the source:
--   - reading: has accuracy 1 − ε on D̃_t → Acc(D̃_t, h_{j*}) ≥ 1 − ε; reason: obvious typo: the proof bounds the error by (T − 1)ε/T ≤ ε and the YES case on p. 22 uses ≥; equality is false (INSIGHTS I2)
--   - generalization: the test's scale σ = (1/δ)√(8TM/(πε)) of (7) → every scale σ > 0; reason: the statement does not depend on σ's value; the σ of (7) is positive, so the lemma specializes to it
--   - encoding: Dict(ε, δ, T, M) for ε > 0 → hypothesis ε ≤ T (with ε > 0); reason: the coordinate probabilities lie in [0, 1] only then; it excludes only parameters for which the test is undefined
-- source:
--   Saket, Intractability of Continual Learning using Parametric Models with Unlimited Replay Buffer, STOC 2027 submission (manuscript sha256 86821df1…), p. 18, Lemma A.5 (PDF p. 19)

import Mathlib
import Definitions.Def_ContinualHardness_Linear_Dataset
import Definitions.Def_ContinualHardness_Linear_Dict

namespace ContinualHardness.Linear

/-- Lemma A.5 (Completeness of `Dict(ε, δ, T, M)`), p. 18, with the printed "accuracy `1 − ε`"
read as "accuracy at least `1 − ε`". For every coordinate `j*`, the dictator classifier
`sign(∑_t x_{tj*})` has accuracy at least `1 − ε` on every `D̃_t`. -/
theorem lemma_A_5 (ε σ : ℝ) (T M : ℕ) (hε : 0 < ε) (hεT : ε ≤ T) (hσ : 0 < σ)
    (jstar : Fin M) (t : Fin T) :
    1 - ε ≤ acc (dictData ε σ T M t) (fun x => sgn (∑ t' : Fin T, x (t', jstar))) := by sorry

end ContinualHardness.Linear
