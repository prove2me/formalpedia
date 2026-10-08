-- Prove2me | Theorems.Thm_BHTOpinion_Approx_lemma1_lipschitz
-- name    : BHTOpinion.Approx.lemma1_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:55.244985+00:00
-- url     : https://prove2.me/theorems/944f3c40-eab4-4b4e-95e3-cc48d7c35077
-- title:
--   Lemma 1 — 𝓛 is Lipschitz at x̃ ∈ X_m: ||𝓛(x̃) − 𝓛(ỹ)||_∞ ≤ (2 + 8/m)||x̃ − ỹ||_∞
-- statement:
--   Let $m>0$, let $\tilde x\in X_m$ (nondecreasing, bounded, with slope at least $m$ on $I=[0,1]$) and let $\tilde y\in Y$ be any bounded measurable opinion function. If $|\tilde x(\gamma)-\tilde y(\gamma)|\le\delta$ for every $\gamma\in I$, then for every $\alpha\in I$
--
--   $$\bigl|\mathcal L(\tilde x)(\alpha)-\mathcal L(\tilde y)(\alpha)\bigr|\le\Bigl(2+\frac8m\Bigr)\delta .$$
--
--   In sup-norm form: $\|\mathcal L(\tilde x)-\mathcal L(\tilde y)\|_\infty\le(2+8/m)\|\tilde x-\tilde y\|_\infty$. The operator $\mathcal L$ is therefore Lipschitz at every point of $X_m$, although it is discontinuous in general. This is the estimate that, along a regular trajectory, gives continuous dependence on the initial condition (Proposition 4).
--
--   **Formalization Note** The sup norms are written pointwise over $I$: the hypothesis is a bound $\delta$ on $|\tilde x-\tilde y|$ at every point of $I$, and the conclusion holds at every point of $I$. This is equivalent to the paper's inequality with $\delta=\|\tilde x-\tilde y\|_\infty$ and avoids a real supremum.
-- source:
--   Blondel, Hendrickx, Tsitsiklis, Continuous-time average-preserving opinion dynamics with opinion-dependent communications, SIAM J. Control Optim. 48 (2010), Lemma 1, p. 5223

import Mathlib
import Definitions.Def_BHTOpinion_Approx_Continuum

namespace BHTOpinion.Approx

theorem lemma1_lipschitz (m : ℝ) (hm : 0 < m) (x y : ℝ → ℝ)
    (hx : BHTOpinion.Continuum.InXm m x) (hy : BHTOpinion.Continuum.InY y) (δ : ℝ) (hδ : ∀ γ ∈ BHTOpinion.Continuum.I, |x γ - y γ| ≤ δ) :
    ∀ α ∈ BHTOpinion.Continuum.I, |BHTOpinion.Continuum.opL x α - BHTOpinion.Continuum.opL y α| ≤ (2 + 8 / m) * δ := by sorry

end BHTOpinion.Approx
