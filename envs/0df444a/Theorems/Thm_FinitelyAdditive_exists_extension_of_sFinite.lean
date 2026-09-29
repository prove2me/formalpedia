-- Prove2me | Theorems.Thm_FinitelyAdditive_exists_extension_of_sFinite
-- name    : FinitelyAdditive.exists_extension_of_sFinite
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T15:07:07.347876+00:00
-- url     : https://prove2.me/theorems/be8340c2-c834-480a-862b-8bce41e7aefc
-- title:
--   A finitely additive extension of an s-finite measure to all subsets
-- statement:
--   Let $\mu$ be an s-finite measure on a measurable space $X$. There is a function $\nu$, defined on every subset of $X$ with values in $[0,\infty]$, with $\nu(\emptyset) = 0$ and $\nu(s \cup t) = \nu(s) + \nu(t)$ for disjoint $s, t$, that agrees with $\mu$ on every $\mu$-null-measurable set. Only finite additivity is asserted; $\nu$ need not be countably additive, and it is not unique.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 7, recalls without proof Carathéodory's extension theorem for finitely additive measures on a Boolean algebra; this is the case of an s-finite measure on a σ-algebra extended to all subsets, proved directly; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
open MeasureTheory
open scoped ENNReal

namespace FinitelyAdditive

theorem exists_extension_of_sFinite {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ] :
    ∃ ν : Set X → ℝ≥0∞, ν ∅ = 0 ∧ (∀ s t : Set X, Disjoint s t → ν (s ∪ t) = ν s + ν t) ∧
      ∀ s : Set X, NullMeasurableSet s μ → ν s = μ s := by
  sorry

end FinitelyAdditive
