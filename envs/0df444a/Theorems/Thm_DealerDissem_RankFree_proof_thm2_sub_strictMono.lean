-- Prove2me | Theorems.Thm_DealerDissem_RankFree_proof_thm2_sub_strictMono
-- name    : DealerDissem.RankFree.proof_thm2_sub_strictMono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:02:21.115752+00:00
-- url     : https://prove2.me/theorems/cdf4743f-aa5b-42ac-a445-32c019f48a85
-- title:
--   Proof of Theorem 2, point 2, p. 42 — $z-\Omega(z)\ge0$ and $z\mapsto z-\Omega(z)$ is increasing
-- statement:
--   Throughout, $\rho>0$ is the sure return of the asset, $r>0$ the funding spread, $q\in(0,1)$ the probability that a dealer is available, and $G$ the distribution of the customer demand $\tilde\omega$, a probability distribution on $\mathbb R_+$ with finite mean; $H(\omega)=\Pr(\tilde\omega\ge\omega)$. Let $\Omega:\mathbb R_+\to\mathbb R$ be bounded, continuous and a solution of the functional equation (9), $$\Omega(0)=0,\qquad \Omega(y)=\sup_{0\le\omega\le y} qH(\omega)\bigl(\omega+\Omega(y-\omega)\bigr)\quad (y>0).$$
--
--   By Theorem 1 this is the collected demand. Then for every $z\ge0$, $z-\Omega(z)\ge0$, and the map $z\mapsto z-\Omega(z)$ is strictly increasing on $\mathbb R_+$.
--
--   $r(z-\Omega(z))$ is the expected net funding cost of a dealer with financing needs $z$. Its monotonicity makes the Theorem 2 acceptance rule a threshold rule in the customer demand.
--
--   **Formalization Note.** $\Omega$ is a function `ℝ → ℝ`; boundedness, continuity and every conclusion are stated on $[0,\infty)$ only, so values at negative arguments never matter. The supremum in (9) is taken over $0\le\omega\le y$, as in (46). "Increasing" is read strictly, as in the proof of Lemma 1 ("$z'-\Omega(z')<z-\Omega(z)$ for $z'<z$"); it follows from $q<1$.
-- source:
--   Colliard & Demange, Asset Dissemination through Dealer Markets, SSRN 3244321 (authors' version of September 17, 2020), p. 42 (PDF 44), proof of Theorem 2, point 2 ("Since z − Ω(z) is increasing"; "z − Ω(z) ≥ 0")

import Mathlib
import Definitions.Def_DealerDissem_RankFree_Model

open MeasureTheory

namespace DealerDissem.RankFree

/-- Proof of Theorem 2, point 2, p. 42: `z − Ω(z) ≥ 0` on `ℝ₊`, and `z ↦ z − Ω(z)` is
(strictly) increasing on `ℝ₊`. -/
theorem proof_thm2_sub_strictMono (P : Params) (μ : Measure ℝ) (hμ : IsDemandDist μ)
    (Ω : ℝ → ℝ) (hΩb : BoundedOnNonneg Ω) (hΩc : ContinuousOn Ω (Set.Ici 0))
    (hΩ : SolvesCollected P μ Ω) :
    (∀ z, 0 ≤ z → 0 ≤ z - Ω z) ∧ StrictMonoOn (fun z => z - Ω z) (Set.Ici 0) := by sorry

end DealerDissem.RankFree
