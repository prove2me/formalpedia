-- Prove2me | Theorems.Thm_ContrastiveDuality_sphere_inner_mean_var
-- name    : ContrastiveDuality.sphere_inner_mean_var
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:35:08.139474+00:00
-- url     : https://prove2.me/theorems/b63b88ad-8df6-4fec-9820-5386b699d93c
-- title:
--   Proposition 3.1 (as proved): mean and variance of the dot product of uniform unit vectors
-- statement:
--   Let $M\ge1$, and let $X,Y$ be independent random vectors on a probability space, each uniformly distributed on the unit sphere $S^{M-1}\subset\mathbb{R}^M$. Then
--
--   $$\mathbb{E}\big[X^TY\big]=0\qquad\text{and}\qquad\operatorname{Var}\big[X^TY\big]=\frac1M.$$
--
--   **Formalization Note** Proposition 3.1 is printed as a claim about the embeddings to which SimCLR and DCL lead with infinitely many negative samples. Its proof cites Theorem 1 of Wang and Isola (2020) for the fact that these embeddings are uniformly distributed on the sphere, and then computes the two moments. The cited asymptotic optimisation result is not a precise statement about finite objects, so the statement formalised is what the proof establishes after that citation: the moments of the dot product of two independent uniform unit vectors. The case $M=1$, which the proof's route through Lemma C.1 does not cover, also satisfies the conclusion and is included because the printed proposition has no restriction on $M$.
-- source:
--   Garrido, Chen, Bardes, Najman and LeCun, On the duality between contrastive and non-contrastive self-supervised learning, arXiv:2206.02574v3 (ICLR 2023), Section 3, Proposition 3.1, eq. (2), p. 3; proof as Proposition C.2, eqs. (24)-(26), p. 15

import Mathlib
import Definitions.Def_ContrastiveDuality_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace ContrastiveDuality

theorem sphere_inner_mean_var {M : ℕ} (hM : 1 ≤ M) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → EuclideanSpace ℝ (Fin M))
    (hX : Measurable X) (hY : Measurable Y)
    (hXlaw : P.map X = uniformSphere M) (hYlaw : P.map Y = uniformSphere M)
    (hXY : IndepFun X Y P) :
    ∫ ω, inner ℝ (X ω) (Y ω) ∂P = 0 ∧
      variance (fun ω => inner ℝ (X ω) (Y ω)) P = 1 / (M : ℝ) := by sorry

end ContrastiveDuality
