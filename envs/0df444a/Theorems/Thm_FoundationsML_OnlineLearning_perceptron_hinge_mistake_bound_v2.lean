-- Prove2me | Theorems.Thm_FoundationsML_OnlineLearning_perceptron_hinge_mistake_bound_v2
-- name    : FoundationsML.OnlineLearning.perceptron_hinge_mistake_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:18:15.84398+00:00
-- url     : https://prove2.me/theorems/88b07eea-450a-46f9-8456-c4a72603097a
-- title:
--   Theorem 8.11 — Perceptron hinge-loss mistake bound (infimum over exactly $\rho>0$, $\|v\|\le1$)
-- statement:
--   **Statement (Theorem 8.11, p. 196, PDF p. 213).** Let $I$ be the set of indices $t\in[T]$ at which the Perceptron algorithm makes an update when processing $x_1,\dots,x_T$ with $\|x_t\|\le r$ for some $r>0$ and labels $y_t\in\{-1,+1\}$. Then the number of updates $M=|I|$ satisfies
--   $$M \le \inf_{\rho>0,\ \|v\|_2\le1}\Bigg[\frac{\frac r\rho+\sqrt{\frac{r^2}{\rho^2}+4\|l_\rho\|_1}}{2}\Bigg]^2,\qquad l_\rho=(l_t)_{t\in I},\ l_t=\max\Big\{0,1-\frac{y_t(v\cdot x_t)}\rho\Big\}.$$
--
--   **Formalization Note.** The retired version wrote the infimum as the bounded `⨅ ρ ∈ Set.Ioi 0, ⨅ v ∈ closedBall 0 1, …`; on $\mathbb R$ this is an infimum over all real $\rho$, and for $\rho\le0$ the inner infimum over the empty index is `sInf ∅ = 0`, so the right-hand side was $0$ (the accepted disproof). The infimum is now `sInf` of the image of exactly the book's index set $\{(\rho,v)\mid\rho>0,\ \|v\|_2\le1\}$, which is nonempty and whose image is bounded below by $0$ (every term is a square), so `sInf` is the book's $\inf_{\rho>0,\|v\|_2\le1}$. As before, only the theorem's first (tighter, $L^1$-norm) inequality is stated, and rounds are $0$-indexed ($t<T$).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 196, Theorem 8.11 (PDF p. 213)

import Mathlib
import Definitions.Def_FoundationsML_OnlineLearning_PerceptronNumUpdates
import Definitions.Def_FoundationsML_OnlineLearning_PerceptronUpdates

namespace FoundationsML.OnlineLearning

/-- Theorem 8.11 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 196, PDF p. 213). Let `I` be the set of update rounds of the Perceptron
algorithm processing `x_1,…,x_T` with `‖x_t‖ ≤ r`. Then `M = |I|` satisfies
`M ≤ inf_{ρ>0, ‖v‖₂≤1} [(r/ρ + sqrt(r²/ρ² + 4‖l_ρ‖₁))/2]²`, where
`l_ρ = (l_t)_{t∈I}` with `l_t = max{0, 1 − y_t(v·x_t)/ρ}`.

**Formalization Note.** Replaces `perceptron_hinge_mistake_bound`, which wrote the infimum as
the bounded `⨅ ρ ∈ Set.Ioi 0, ⨅ v ∈ closedBall 0 1, …`; on `ℝ` this is an infimum over *all*
real `ρ`, and for `ρ ≤ 0` the inner infimum over the empty index is `sInf ∅ = 0`, so the whole
right-hand side was `0` (the disproof). The infimum is now `sInf` of the image of exactly the
book's index set `{(ρ, v) | ρ > 0, ‖v‖₂ ≤ 1}` (nonempty, and bounded below by `0` since every
term is a square), i.e. the book's `inf_{ρ>0, ‖v‖₂≤1}`. Only the theorem's first (tighter,
`L¹`-norm) inequality is stated, as before; rounds are `0`-indexed (`t < T`). -/
theorem perceptron_hinge_mistake_bound_v2
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (x : ℕ → V) (y : ℕ → ℝ) (hy : ∀ t, y t = 1 ∨ y t = -1)
    (T : ℕ) (r : ℝ) (hr : 0 < r) (hxr : ∀ t < T, ‖x t‖ ≤ r) :
    (PerceptronNumUpdates x y T : ℝ) ≤
      sInf ((fun q : ℝ × V =>
        ((r / q.1 + Real.sqrt (r ^ 2 / q.1 ^ 2 +
            4 * ∑ t ∈ PerceptronUpdates x y T,
              max 0 (1 - y t * (inner (𝕜 := ℝ) q.2 (x t) : ℝ) / q.1))) /
          2) ^ 2) '' {q : ℝ × V | 0 < q.1 ∧ ‖q.2‖ ≤ 1}) := by sorry

end FoundationsML.OnlineLearning
