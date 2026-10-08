-- Prove2me | Theorems.Thm_BHTOpinion_Continuum_lemma2_rate_bounds
-- name    : BHTOpinion.Continuum.lemma2_rate_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:54.424507+00:00
-- url     : https://prove2.me/theorems/64fb31fd-3a94-4c7f-8532-f492f600390f
-- title:
--   Lemma 2 — −(x̃(β) − x̃(α)) ≤ 𝓛(x̃)(β) − 𝓛(x̃)(α), and ≤ (2/m)(x̃(β) − x̃(α)) when x̃ ∈ X_m
-- statement:
--   Let $\tilde x\in Y$ be a bounded measurable opinion function on $I=[0,1]$ and let $\alpha,\beta\in I$ with $\tilde x(\alpha)\le\tilde x(\beta)$. Then
--
--   $$\mathcal L(\tilde x)(\beta)-\mathcal L(\tilde x)(\alpha)\ \ge\ -\bigl(\tilde x(\beta)-\tilde x(\alpha)\bigr).$$
--
--   Furthermore, if $\tilde x\in X_m$ for some $m>0$, then
--
--   $$\mathcal L(\tilde x)(\beta)-\mathcal L(\tilde x)(\alpha)\ \le\ \frac 2m\bigl(\tilde x(\beta)-\tilde x(\alpha)\bigr).$$
--
--   The lemma bounds the rate at which the opinions of two agents can approach or separate. The first part shows that the gap between two agents shrinks at most exponentially fast, so increasing initial opinion profiles stay increasing; the second part keeps the upper increase rate under control.
--
--   **Formalization Note** The paper's hypothesis is printed "$x(\alpha)\le x(\beta)$"; it is read as $\tilde x(\alpha)\le\tilde x(\beta)$. The two parts are the two conjuncts of the statement; the second quantifies over every $m>0$ with $\tilde x\in X_m$.
-- source:
--   Blondel, Hendrickx, Tsitsiklis, SIAM J. Control Optim. 48 (2010), Lemma 2, p. 5224

import Mathlib
import Definitions.Def_BHTOpinion_Continuum_Model

open MeasureTheory Filter Topology

namespace BHTOpinion.Continuum

theorem lemma2_rate_bounds (x : ℝ → ℝ) (hx : InY x) (α β : ℝ)
    (hα : α ∈ I) (hβ : β ∈ I) (hle : x α ≤ x β) :
    -(x β - x α) ≤ opL x β - opL x α ∧
      ∀ m : ℝ, 0 < m → InXm m x → opL x β - opL x α ≤ 2 / m * (x β - x α) := by sorry

end BHTOpinion.Continuum
