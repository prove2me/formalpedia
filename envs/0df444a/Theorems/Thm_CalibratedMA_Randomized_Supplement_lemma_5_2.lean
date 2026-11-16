-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_Supplement_lemma_5_2
-- name    : CalibratedMA.Randomized.Supplement.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:25:24.299653+00:00
-- url     : https://prove2.me/theorems/c9c6fb68-3b49-41d0-9ac7-e5851b994954
-- title:
--   Lemma 5.2 — Category averaging as projection
-- statement:
--   Let $(X,Y)\sim D$ have $Y\in[0,1]$, let $S:X\to[0,1]$ be measurable, and let $J$ be a measurable assignment to finitely many categories. With $P=D_X$, write $p_J=\mathbb E_P[S\mid J]$, $R_J=S-p_J$ and $C_J=\{J^{-1}(j)\}_j$. Then all the following identities hold:
--   $$\mathbb E_P[R_J\mid J]=0\quad\text{almost surely},\qquad\mathbb E_P[SR_J]=\mathbb E_P[R_J^2],$$
--   $$\mathbb E_P[gR_J]=\sum_jP(J=j)\operatorname{Cov}_P(g,S\mid J=j)$$
--   for every bounded measurable real test $g$, and
--   $$\mathrm{Cal}_{C_J}(p_J)=\max_{\sigma\in\{-1,1\}^J}|\mathbb E_D[\sigma_{J(X)}(Y-S(X))]|.$$
--   These are all of (7), (8) and (9), supporting Theorem 5.1. Empty categories contribute zero.
--
--   Differences from the source:
--   - encoding: labels in [0,1] or in {0,1} → real labels with the corresponding almost-sure support predicate; reason: the measures are the same labeled laws
--   - encoding: finite categories and a bounded test → Fin r categories, Boolean signs, and a measurable real test with an existential uniform bound; reason: finite relabeling and the ordinary measurability convention preserve all expectations
--   - encoding: conditional projection identities → context marginal D.map Prod.fst, explicit category integrals and almost-everywhere conditional equality; reason: the displayed conditional identities are version-independent; zero-mass categories contribute zero
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026; title page November 2, 2026), p. 21-22, Lemma 5.2 (PDF pp. 23-24)

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Supplement_Categories

open MeasureTheory

namespace CalibratedMA.Randomized.Supplement

/-- Lemma 5.2, pp.21–22: all identities (7), (8), (9). -/
theorem lemma_5_2 (X : Type) [MeasurableSpace X] (D : Measure (X × ℝ))
    (hD : IsLabeledDist D) (S : X → ℝ) (hS : IsDetPredictor S)
    (r : ℕ) (J : X → Fin r) (hJ : Measurable J) :
    let P := D.map Prod.fst
    let R := categoryResidual P S J
    (P[R | MeasurableSpace.comap J inferInstance] =ᵐ[P] 0) ∧
    (∫ x, S x * R x ∂P) = (∫ x, R x ^ 2 ∂P) ∧
    (∀ g : X → ℝ, Measurable g → (∃ M : ℝ, ∀ x, |g x| ≤ M) →
      (∫ x, g x * R x ∂P) =
        ∑ j : Fin r, (P {x | J x = j}).toReal * categoryCovariance P S g J j) ∧
    cellCalibration D (categoryPredictor P S J) J = categorySignMaximum D S J := by sorry

end CalibratedMA.Randomized.Supplement
