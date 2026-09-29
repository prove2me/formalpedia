-- Prove2me | Theorems.Thm_FinitelyAdditive_exists_extension_of_isSetRing
-- name    : FinitelyAdditive.exists_extension_of_isSetRing
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T16:04:42.220829+00:00
-- url     : https://prove2.me/theorems/f5d887ac-da22-470b-b85e-ffb4d158b540
-- title:
--   A finitely additive measure on a ring of sets extends to all subsets
-- statement:
--   Let $X$ be a set and $\mathcal{R}$ a ring of subsets of $X$: it contains $\emptyset$ and is closed under finite unions and differences. Let $\mu : \mathcal{R} \to [0,\infty]$ satisfy $\mu(\emptyset) = 0$ and $\mu(s \cup t) = \mu(s) + \mu(t)$ for disjoint $s, t \in \mathcal{R}$. Then there is $\nu : \mathcal{P}(X) \to [0,\infty]$, defined on every subset of $X$, with
--
--   $$\nu(\emptyset) = 0, \qquad \nu(s \cup t) = \nu(s) + \nu(t) \ \text{ for disjoint } s, t \subseteq X, \qquad \nu|_{\mathcal{R}} = \mu.$$
--
--   This is the finitely additive extension theorem that Garrido recalls as Carathéodory's Extension Theorem in the statement of the Invariant Extension Theorem: restricting $\nu$ to a Boolean algebra of subsets of $X$ that contains $\mathcal{R}$ extends $\mu$ to that algebra. Only finite additivity is asserted, and $\nu$ is not unique. Unlike Carathéodory's $\sigma$-additive extension theorem, it involves no outer measure and no measurability.
--
--   **Formalization Note.** $\mu$ is a function on all subsets of $X$, but only its values on $\mathcal{R}$ enter the hypotheses. The ring is Mathlib's `IsSetRing`, which does not require $X \in \mathcal{R}$.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 7, in the statement of Theorem 2.6: "Recall Carathéodory's Extension Theorem: If $\mathcal{R}$ is a subring of the boolean algebra $\mathcal{A}$ and $\mu$ is a measure on $\mathcal{R}$, then $\mu$ can be extended to a measure $\bar\mu$ on $\mathcal{A}$." The measures in the source are finitely additive throughout, and here the Boolean algebra is an algebra of subsets; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
open MeasureTheory
open scoped ENNReal

namespace FinitelyAdditive

theorem exists_extension_of_isSetRing {X : Type*} {R : Set (Set X)} (hR : IsSetRing R)
    (μ : Set X → ℝ≥0∞) (h0 : μ ∅ = 0)
    (hadd : ∀ s ∈ R, ∀ t ∈ R, Disjoint s t → μ (s ∪ t) = μ s + μ t) :
    ∃ ν : Set X → ℝ≥0∞, ν ∅ = 0 ∧ (∀ s t : Set X, Disjoint s t → ν (s ∪ t) = ν s + ν t) ∧
      ∀ s ∈ R, ν s = μ s := by
  sorry

end FinitelyAdditive
