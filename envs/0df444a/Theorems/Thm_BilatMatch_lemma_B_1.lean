-- Prove2me | Theorems.Thm_BilatMatch_lemma_B_1
-- name    : BilatMatch.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:12:25.102434+00:00
-- url     : https://prove2.me/theorems/ec57cd5a-77d3-48fc-a591-cb749b90bc78
-- title:
--   Lemma B.1 — ironed scores satisfy $\bar\phi^\alpha(v)\le(1+\alpha)v$ and $\bar\tau^\alpha(c)\ge(1+\alpha)c$
-- statement:
--   For every $\alpha\ge0$ and every finitely supported prior, the ironed $\alpha$-virtual values and costs satisfy
--   $$\bar\phi^\alpha(v)\le(1+\alpha)v,\qquad \bar\tau^\alpha(c)\ge(1+\alpha)c$$
--   at every report.
--
--   These bounds guarantee that an edge with positive ironed weight has positive actual surplus.
--
--   **Formalization Note** Ironed scores are the slopes of the greatest convex minorant of the cumulative score curve (p.31), equivalently the pooled block means (p.13).
--
--   Differences from the source:
--   - reading: at every report → at every atom of the prior; reason: the reports of a finite-prior market are the support points (p.6); the ironed scores are defined there
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), Lemma B.1, p.30 (pdf p.32)

import Mathlib
import Definitions.Def_BilatMatch_iron

open MeasureTheory

namespace BilatMatch

/-- **Lemma B.1.** Liu, Qin, Wang, arXiv:2609.30702 (held version, sha256 ff1490ad…), Lemma B.1,
p.30 (pdf p.32).

For every `α ≥ 0` and every finitely supported prior, the ironed `α`-virtual values and costs satisfy
`ϕ̄^α(v) ≤ (1 + α) v` and `τ̄^α(c) ≥ (1 + α) c` at every report.

**Formalization Note** The reports of a finite-prior market are the atoms of the prior (p.6). The
ironed scores are the slopes of the greatest convex minorant of the cumulative `α`-virtual-score
curve over each atom's mass interval (p.31), which is the result of pooling adjacent blocks with
decreasing probability-weighted means (p.13). -/
theorem lemma_B_1 (α : ℝ) (hα : 0 ≤ α) (μ : Measure ℝ) (hμ : IsFiniteSupport μ) :
    (∀ v ∈ atoms μ, ironedValue α μ v ≤ (1 + α) * v) ∧
    (∀ c ∈ atoms μ, (1 + α) * c ≤ ironedCost α μ c) := by sorry

end BilatMatch
