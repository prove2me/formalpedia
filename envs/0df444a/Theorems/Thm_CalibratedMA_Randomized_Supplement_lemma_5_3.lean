-- Prove2me | Theorems.Thm_CalibratedMA_Randomized_Supplement_lemma_5_3
-- name    : CalibratedMA.Randomized.Supplement.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:25:57.248073+00:00
-- url     : https://prove2.me/theorems/a43584d2-3f82-4052-a052-a0c27895ed82
-- title:
--   Lemma 5.3 — Population category assignment
-- statement:
--   Fix any context probability law $P$ and the complete finite assignment construction of Section 5.2: a nonempty finite $G$, signed tests $H=G\cup(-G)$, measurable score $S$, finite measurable cell partition, private singleton set, $K,m\ge1$ and $\lambda>0$. Put $w=(\lambda+2)/K$ and $e_{\rm app}=w/2+1/\sqrt m$. There is one distribution $\pi_\star$ on $H$ for which both bounds hold:
--   $$\max_{h\in H}d_h(\pi_\star)\le\frac{e_{\rm app}^2}{4\lambda},\qquad
--   \bar V(\pi_\star)\le\frac{e_{\rm app}^2}{\lambda^2}.$$
--   Here $d_h$ and $\bar V$ average the residual change and squared score change under the actual independent assignment law. The mixture may depend on $P$ and the construction. This population existence result supports Theorem 5.1 and assumes no optimality or error bound.
--
--   Differences from the source:
--   - encoding: Section 5.2 partition, signed tests and tuples → AssignmentConfig, finite indices for the distinct signed functions, and an actual finite product measure; reason: this is the source construction, not arbitrary predictors with assumed residual bounds
--   - encoding: a maximum bound over H → the inequality for every h in the finite nonempty H; reason: equivalent to the finite maximum bound
--   - encoding: only nonprivate cells receive draws → independent unused draws at private cells are also present; reason: integrating out ignored coordinates leaves exactly the source assignment law
-- source:
--   Jiuyao Lu, Georgy Noarov, Aaron Roth, Calibrated Multiaccuracy: Deterministic and Randomized Sample Complexity, STOC 2027 submission #900 (October 2026; title page November 2, 2026), p. 24, Lemma 5.3 (PDF pp. 26)

import Mathlib
import Definitions.Def_CalibratedMA_Randomized_Supplement_Assignment

open MeasureTheory

namespace CalibratedMA.Randomized.Supplement

/-- Lemma 5.3, p.24: the same mixture satisfies both bounds. -/
theorem lemma_5_3 (X : Type) [MeasurableSpace X] (P : Measure X)
    (hP : IsProbabilityMeasure P) (c : AssignmentConfig X) :
    ∃ π : Measure (Fin (signedTests c.G).card), IsProbabilityMeasure π ∧
      (∀ h ∈ signedTests c.G, meanChange c P π h ≤ approximationError c ^ 2 / (4 * c.lam)) ∧
      meanVariance c P π ≤ approximationError c ^ 2 / c.lam ^ 2 := by sorry

end CalibratedMA.Randomized.Supplement
