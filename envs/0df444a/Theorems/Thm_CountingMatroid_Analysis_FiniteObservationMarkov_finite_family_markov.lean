-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_FiniteObservationMarkov_finite_family_markov
-- name    : CountingMatroid.Analysis.FiniteObservationMarkov.finite_family_markov
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T14:12:46.300974+00:00
-- url     : https://prove2.me/theorems/953ba54d-476f-40c5-9b05-f0e792ada12e
-- title:
--   A finite-family Markov bound for a covered bad event
-- statement:
--   Let $X,I$ be finite types, let $A\subseteq X$ be a bad event, and let $e:X\times I\to\mathbb Q$ be nonnegative. Let $w,\theta,b\in\mathbb Q$ satisfy $w\ge0$ and $\theta>0$. Assume every bad outcome has some index with error at least $\theta$, and assume each indexed error has weighted total at most $b$:
--
--   $$x\in A\Longrightarrow\exists i\in I:\ e(x,i)\ge\theta,\qquad w\sum_{x\in X}e(x,i)\le b\quad(i\in I).$$
--
--   Then
--
--   $$|A|w\le\frac{|I|b}{\theta}.$$
--
--   The weight $w$ need not normalize the outcome space. No independence assumption is used.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FiniteObservationMarkov.lean#L86-L110

import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Infix
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic

namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
set_option autoImplicit false

namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FiniteObservationMarkov

open CountingMatroid.Analysis.RelativeObservationBounds

theorem CountingMatroid.Analysis.FiniteObservationMarkov.finite_family_markov {α β : Type} [Fintype α] [Fintype β]
    (bad : α → Prop) (error : α → β → ℚ) (weight threshold bound : ℚ)
    (hweight : 0 ≤ weight) (hthreshold : 0 < threshold)
    (herror : ∀ x i, 0 ≤ error x i)
    (hbad : ∀ x, bad x → ∃ i, threshold ≤ error x i)
    (hmoment : ∀ i, (∑ x, error x i) * weight ≤ bound) :
    letI := Classical.propDecidable
    ((Finset.univ.filter bad).card : ℚ) * weight ≤
      (Fintype.card β : ℚ) * bound / threshold := by sorry
