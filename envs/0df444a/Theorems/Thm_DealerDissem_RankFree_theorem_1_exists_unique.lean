-- Prove2me | Theorems.Thm_DealerDissem_RankFree_theorem_1_exists_unique
-- name    : DealerDissem.RankFree.theorem_1_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:22.379382+00:00
-- url     : https://prove2.me/theorems/c46a588e-2497-4dea-a8d1-17c63676cb0d
-- title:
--   Theorem 1, p. 14 — there is a unique bounded continuous function $\Omega$ satisfying (9)
-- statement:
--   Throughout, $\rho>0$ is the sure return of the asset, $r>0$ the funding spread, $q\in(0,1)$ the probability that a dealer is available, and $G$ the distribution of the customer demand $\tilde\omega$, a probability distribution on $\mathbb R_+$ with finite mean; $H(\omega)=\Pr(\tilde\omega\ge\omega)$. Consider the functional equation (9):
--   $$\Omega(0)=0,\qquad \Omega(y)=\sup_{0\le\omega\le y} qH(\omega)\bigl(\omega+\Omega(y-\omega)\bigr)\quad\text{for all }y>0.$$
--   There exists a function $\Omega$ on $\mathbb R_+$ that is bounded, continuous and satisfies (9), and any two such functions coincide on $\mathbb R_+$.
--
--   The unique solution is the **collected demand**: the customer demand that a dealer with financing needs $y$ can expect to collect from the rest of the chain. It is the input of the equilibrium construction of Theorem 2.
--
--   **Formalization Note.** $\Omega$ is a function `ℝ → ℝ`; boundedness, continuity and every conclusion are stated on $[0,\infty)$ only, so values at negative arguments never matter. The supremum in (9) is taken over $0\le\omega\le y$, as in (46).
-- source:
--   Colliard & Demange, Asset Dissemination through Dealer Markets, SSRN 3244321 (authors' version of September 17, 2020), p. 14 (PDF 16), Theorem 1, first sentence; (9) on p. 13 (PDF 15)

import Mathlib
import Definitions.Def_DealerDissem_RankFree_Model

open MeasureTheory

namespace DealerDissem.RankFree

/-- Theorem 1, first sentence, p. 14: there is a unique function `Ω` that is bounded,
continuous (on `ℝ₊`) and satisfies (9); uniqueness is on `ℝ₊`. -/
theorem theorem_1_exists_unique (P : Params) (μ : Measure ℝ) (hμ : IsDemandDist μ) :
    (∃ Ω : ℝ → ℝ, BoundedOnNonneg Ω ∧ ContinuousOn Ω (Set.Ici 0) ∧ SolvesCollected P μ Ω) ∧
    ∀ Ω₁ Ω₂ : ℝ → ℝ,
      BoundedOnNonneg Ω₁ → ContinuousOn Ω₁ (Set.Ici 0) → SolvesCollected P μ Ω₁ →
      BoundedOnNonneg Ω₂ → ContinuousOn Ω₂ (Set.Ici 0) → SolvesCollected P μ Ω₂ →
      Set.EqOn Ω₁ Ω₂ (Set.Ici 0) := by sorry

end DealerDissem.RankFree
