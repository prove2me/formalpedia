-- Prove2me | Theorems.Thm_DealerDissem_RankFree_theorem_1_lipschitz_monotone
-- name    : DealerDissem.RankFree.theorem_1_lipschitz_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:20.67909+00:00
-- url     : https://prove2.me/theorems/bfc1d1ce-2c34-41cd-9449-db75a01cbf5c
-- title:
--   Theorem 1, p. 14 — the collected demand $\Omega$ is Lipschitz with constant $q$ and non-decreasing
-- statement:
--   Throughout, $\rho>0$ is the sure return of the asset, $r>0$ the funding spread, $q\in(0,1)$ the probability that a dealer is available, and $G$ the distribution of the customer demand $\tilde\omega$, a probability distribution on $\mathbb R_+$ with finite mean; $H(\omega)=\Pr(\tilde\omega\ge\omega)$. Let $\Omega:\mathbb R_+\to\mathbb R$ be bounded, continuous and a solution of the functional equation (9), $$\Omega(0)=0,\qquad \Omega(y)=\sup_{0\le\omega\le y} qH(\omega)\bigl(\omega+\Omega(y-\omega)\bigr)\quad (y>0).$$
--
--   By Theorem 1 this is the collected demand. Then for all $x,y\ge0$
--   $$|\Omega(x)-\Omega(y)|\le q\,|x-y|,$$
--   and $\Omega$ is non-decreasing on $\mathbb R_+$.
--
--   These regularity properties are used throughout the proof of Theorem 2, in particular through Lemma A.2.
--
--   **Formalization Note.** $\Omega$ is a function `ℝ → ℝ`; boundedness, continuity and every conclusion are stated on $[0,\infty)$ only, so values at negative arguments never matter. The supremum in (9) is taken over $0\le\omega\le y$, as in (46).
-- source:
--   Colliard & Demange, Asset Dissemination through Dealer Markets, SSRN 3244321 (authors' version of September 17, 2020), p. 14 (PDF 16), Theorem 1 ("Moreover, the function Ω is lipshitz with constant q and non-decreasing")

import Mathlib
import Definitions.Def_DealerDissem_RankFree_Model

open MeasureTheory

namespace DealerDissem.RankFree

/-- Theorem 1, p. 14: `Ω` is Lipschitz with constant `q` and non-decreasing on `ℝ₊`. -/
theorem theorem_1_lipschitz_monotone (P : Params) (μ : Measure ℝ) (hμ : IsDemandDist μ)
    (Ω : ℝ → ℝ) (hΩb : BoundedOnNonneg Ω) (hΩc : ContinuousOn Ω (Set.Ici 0))
    (hΩ : SolvesCollected P μ Ω) :
    (∀ x y, 0 ≤ x → 0 ≤ y → |Ω x - Ω y| ≤ P.q * |x - y|) ∧ MonotoneOn Ω (Set.Ici 0) := by sorry

end DealerDissem.RankFree
