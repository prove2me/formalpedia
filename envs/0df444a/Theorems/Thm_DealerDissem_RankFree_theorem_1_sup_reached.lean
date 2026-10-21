-- Prove2me | Theorems.Thm_DealerDissem_RankFree_theorem_1_sup_reached
-- name    : DealerDissem.RankFree.theorem_1_sup_reached
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:14.844835+00:00
-- url     : https://prove2.me/theorems/adb65bd3-3fbc-484f-8ff0-0cbbf3fcec18
-- title:
--   Theorem 1, p. 14 — the supremum in (9) is reached: the targeted values $\mathcal T(y)$ of (10) are nonempty
-- statement:
--   Throughout, $\rho>0$ is the sure return of the asset, $r>0$ the funding spread, $q\in(0,1)$ the probability that a dealer is available, and $G$ the distribution of the customer demand $\tilde\omega$, a probability distribution on $\mathbb R_+$ with finite mean; $H(\omega)=\Pr(\tilde\omega\ge\omega)$. Let $\Omega:\mathbb R_+\to\mathbb R$ be bounded, continuous and a solution of the functional equation (9), $$\Omega(0)=0,\qquad \Omega(y)=\sup_{0\le\omega\le y} qH(\omega)\bigl(\omega+\Omega(y-\omega)\bigr)\quad (y>0).$$
--
--   By Theorem 1 this is the collected demand. Then for every $y\ge0$ the supremum in (9) is reached: there is $\omega\in\mathcal T(y)$, where
--   $$\mathcal T(y)=\arg\max_{0\le\omega\le y} qH(\omega)\bigl(\omega+\Omega(y-\omega)\bigr),$$
--   and $\Omega(y)=qH(\omega)(\omega+\Omega(y-\omega))$ at that $\omega$.
--
--   $\mathcal T(y)$ is the set of **targeted values**: the customer demands that a dealer with financing needs $y$ optimally targets. Its nonemptiness is what makes a selection $T$ of $\mathcal T$, used in Theorem 2, exist.
--
--   **Formalization Note.** $\Omega$ is a function `ℝ → ℝ`; boundedness, continuity and every conclusion are stated on $[0,\infty)$ only, so values at negative arguments never matter. The supremum in (9) is taken over $0\le\omega\le y$, as in (46).
-- source:
--   Colliard & Demange, Asset Dissemination through Dealer Markets, SSRN 3244321 (authors' version of September 17, 2020), p. 14 (PDF 16), Theorem 1, second sentence, (10)

import Mathlib
import Definitions.Def_DealerDissem_RankFree_Model

open MeasureTheory

namespace DealerDissem.RankFree

/-- Theorem 1, second sentence, p. 14: the supremum in (9) is reached, i.e. the set of
targeted values `𝒯(y)` of (10) is nonempty and `Ω(y)` is the value of the objective there. -/
theorem theorem_1_sup_reached (P : Params) (μ : Measure ℝ) (hμ : IsDemandDist μ)
    (Ω : ℝ → ℝ) (hΩb : BoundedOnNonneg Ω) (hΩc : ContinuousOn Ω (Set.Ici 0))
    (hΩ : SolvesCollected P μ Ω) :
    ∀ y, 0 ≤ y → ∃ ω ∈ targets P μ Ω y, Ω y = objective P μ Ω y ω := by sorry

end DealerDissem.RankFree
