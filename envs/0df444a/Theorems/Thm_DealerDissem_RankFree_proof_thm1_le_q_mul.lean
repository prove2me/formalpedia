-- Prove2me | Theorems.Thm_DealerDissem_RankFree_proof_thm1_le_q_mul
-- name    : DealerDissem.RankFree.proof_thm1_le_q_mul
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:20.321495+00:00
-- url     : https://prove2.me/theorems/c7dbfd94-22aa-46f4-9d56-dca3c49e136a
-- title:
--   Proof of Theorem 1, p. 41 — the collected demand satisfies $\Omega(z)\le qz$
-- statement:
--   Throughout, $\rho>0$ is the sure return of the asset, $r>0$ the funding spread, $q\in(0,1)$ the probability that a dealer is available, and $G$ the distribution of the customer demand $\tilde\omega$, a probability distribution on $\mathbb R_+$ with finite mean; $H(\omega)=\Pr(\tilde\omega\ge\omega)$. Let $\Omega:\mathbb R_+\to\mathbb R$ be bounded, continuous and a solution of the functional equation (9), $$\Omega(0)=0,\qquad \Omega(y)=\sup_{0\le\omega\le y} qH(\omega)\bigl(\omega+\Omega(y-\omega)\bigr)\quad (y>0).$$
--
--   By Theorem 1 this is the collected demand. Then for every $z\ge0$,
--   $$\Omega(z)\le q\,z.$$
--
--   A consequence of $q$-Lipschitz continuity and $\Omega(0)=0$, used repeatedly in the analysis of the equilibrium (for instance $z-\Omega(z)\ge(1-q)z\ge0$).
--
--   **Formalization Note.** $\Omega$ is a function `ℝ → ℝ`; boundedness, continuity and every conclusion are stated on $[0,\infty)$ only, so values at negative arguments never matter. The supremum in (9) is taken over $0\le\omega\le y$, as in (46).
-- source:
--   Colliard & Demange, Asset Dissemination through Dealer Markets, SSRN 3244321 (authors' version of September 17, 2020), p. 41 (PDF 43), proof of Theorem 1 ("Since Ω(0) = 0, this implies in particular that Ω(z) ≤ qz")

import Mathlib
import Definitions.Def_DealerDissem_RankFree_Model

open MeasureTheory

namespace DealerDissem.RankFree

/-- Proof of Theorem 1, p. 41: `Ω(z) ≤ q z` for every `z ≥ 0`. -/
theorem proof_thm1_le_q_mul (P : Params) (μ : Measure ℝ) (hμ : IsDemandDist μ)
    (Ω : ℝ → ℝ) (hΩb : BoundedOnNonneg Ω) (hΩc : ContinuousOn Ω (Set.Ici 0))
    (hΩ : SolvesCollected P μ Ω) :
    ∀ z, 0 ≤ z → Ω z ≤ P.q * z := by sorry

end DealerDissem.RankFree
