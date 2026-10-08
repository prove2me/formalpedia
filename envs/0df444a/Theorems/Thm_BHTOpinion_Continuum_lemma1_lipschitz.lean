-- Prove2me | Theorems.Thm_BHTOpinion_Continuum_lemma1_lipschitz
-- name    : BHTOpinion.Continuum.lemma1_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:20.694479+00:00
-- url     : https://prove2.me/theorems/f09970c6-3bb2-4ab4-8f59-13349e16c785
-- title:
--   Lemma 1 — 𝓛 is Lipschitz at x̃ ∈ X_m with constant 2 + 8/m
-- statement:
--   Let $m>0$, let $\tilde x\in X_m$ (nondecreasing on $I=[0,1]$ with increase rate at least $m$), and let $\tilde y\in Y$ be any bounded measurable opinion function. Write $\mathcal L$ for the interaction operator (3.3). If $|\tilde x(\gamma)-\tilde y(\gamma)|\le\delta$ for every $\gamma\in I$, then for every $\alpha\in I$
--
--   $$\bigl|\mathcal L(\tilde x)(\alpha)-\mathcal L(\tilde y)(\alpha)\bigr|\le\Bigl(2+\frac 8m\Bigr)\delta .$$
--
--   Equivalently, $\|\mathcal L(\tilde x)-\mathcal L(\tilde y)\|_\infty\le(2+8/m)\|\tilde x-\tilde y\|_\infty$: the operator $\mathcal L$, although discontinuous in general, is Lipschitz at every function whose opinions increase at a positive rate. This is what makes the solution operator of (3.2) a contraction on short time intervals.
--
--   **Formalization Note** The sup-norm inequality is stated for every bound $\delta$ on $\sup_{\gamma\in I}|\tilde x(\gamma)-\tilde y(\gamma)|$ and every $\alpha\in I$, rather than with a real supremum; this is equivalent and avoids a junk value of an unbounded supremum.
-- source:
--   Blondel, Hendrickx, Tsitsiklis, SIAM J. Control Optim. 48 (2010), Lemma 1, p. 5223

import Mathlib
import Definitions.Def_BHTOpinion_Continuum_Model

open MeasureTheory Filter Topology

namespace BHTOpinion.Continuum

theorem lemma1_lipschitz (m : ℝ) (hm : 0 < m) (x y : ℝ → ℝ)
    (hx : InXm m x) (hy : InY y) (δ : ℝ) (hδ : ∀ γ ∈ I, |x γ - y γ| ≤ δ) :
    ∀ α ∈ I, |opL x α - opL y α| ≤ (2 + 8 / m) * δ := by sorry

end BHTOpinion.Continuum
