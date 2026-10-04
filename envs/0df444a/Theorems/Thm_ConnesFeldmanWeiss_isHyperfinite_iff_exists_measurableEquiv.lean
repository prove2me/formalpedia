-- Prove2me | Theorems.Thm_ConnesFeldmanWeiss_isHyperfinite_iff_exists_measurableEquiv
-- name    : ConnesFeldmanWeiss.isHyperfinite_iff_exists_measurableEquiv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T14:15:03.694994+00:00
-- url     : https://prove2.me/theorems/f2b1fd36-4940-4e9f-880f-6de358364334
-- title:
--   §1 (external, Dye) — a relation is hyperfinite exactly when, up to a null set, one Borel automorphism generates it
-- statement:
--   Throughout, $X$ is a standard Borel space, $\mu$ a $\sigma$-finite measure on $X$, and $R \subseteq X \times X$ a discrete measured equivalence relation for $\mu$ (`IsDiscreteMeasured`): a Borel equivalence relation whose classes are countable and for which $\mu$ is quasi-invariant (the saturation of a null Borel set is null).
--
--   Then $R$ is hyperfinite (`IsHyperfinite`) if and only if there are a Borel automorphism $T$ of $X$ (a bijection, measurable with measurable inverse) and a $\mu$-null Borel set $N$ such that, for every $x \notin N$ and every $y \in X$, $(x, y) \in R$ exactly when $y = T^n x$ for some $n \in \mathbb Z$: off $N$, the $R$-class of $x$ is the $T$-orbit of $x$.
--
--   “Up to an $m$-null set” is read through the first coordinate: since $m$ integrates over $x$ the counting measure on the class of $x$, a set of pairs is $m$-null exactly when $\mu$-almost every $x$ has no point of it in its section. $T$ is not assumed non-singular.
-- source:
--   Dye, H. A., On groups of measure preserving transformations. I, Amer. J. Math. 81 (1959) 119–159, https://doi.org/10.2307/2372852, p. 434, §1

import Mathlib
import Definitions.Def_ConnesFeldmanWeiss

namespace ConnesFeldmanWeiss

theorem isHyperfinite_iff_exists_measurableEquiv {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite μ]
    (R : Set (X × X)) (hR : IsDiscreteMeasured μ R) :
    IsHyperfinite μ R ↔ ∃ T : X ≃ᵐ X, ∃ N : Set X, MeasurableSet N ∧ μ N = 0 ∧
      ∀ x, x ∉ N → ∀ y, ((x, y) ∈ R ↔ ∃ n : ℤ, (T.toEquiv ^ n) x = y) := by
  sorry

end ConnesFeldmanWeiss
