-- Prove2me | Theorems.Thm_CircletTSP_Facet_theorem_5_1
-- name    : CircletTSP.Facet.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:23.952457+00:00
-- url     : https://prove2.me/theorems/2c8c26ad-1a26-4dfe-93de-4ed19424d3ce
-- title:
--   Theorem 5.1, p. 20 — for 4 ∣ n the circlet inequality is valid for STSP(n) and defines a facet of it
-- statement:
--   Let $n$ be a positive multiple of $4$ and $d=n/2$. The circlet inequality
--   $$\sum_{i=1}^{d} c_i t_i\ \ge\ n-2,\qquad c_i=\begin{cases} i, & i\text{ odd},\\ d-i, & i \text{ even},\end{cases}$$
--   is facet defining for the symmetric traveling salesman polytope $STSP(n)$:
--
--   1. it is valid: every $x\in STSP(n)$ satisfies it;
--   2. the face $F=\{x\in STSP(n):\ \sum_{i=1}^{d} c_i t_i(x)=n-2\}$ is a facet of $STSP(n)$, i.e. a nonempty face with $\dim F=\dim STSP(n)-1$.
--
--   This is the main result of the paper: the circlet inequality, whose coefficients depend only on edge lengths around a circle (a circulant inequality), is not merely valid but one of the inequalities in any minimal linear description of $STSP(n)$.
--
--   **Formalization Note** $STSP(n)$ is the convex hull of the incidence vectors `MetricTSP.tourVec π`, in ordered-pair coordinates. "Facet" is the published `Disjunctive.Polarity.IsFacet`: an extreme subset, nonempty, of affine dimension one less than $STSP(n)$. Validity is conjoined explicitly, since `IsFacet` alone would also hold for the reversed inequality. $0<n$ is added: $4\mid 0$, but $STSP(0)$ is a single point and the facet claim fails there.
-- source:
--   Gutekunst, Williamson, The Circlet Inequalities, arXiv:2012.12363v1, p. 20, Theorem 5.1 (facet defining as defined on p. 2)

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection
import Definitions.Def_CircletTSP_Facet_Setting

namespace CircletTSP.Facet

/-- Theorem 5.1 (p. 20): for `4 ∣ n`, the circlet inequality `∑_{i=1}^{d} c_i t_i ≥ n - 2` is
facet defining for `STSP(n)`: it is valid on `STSP(n)`, and the points of `STSP(n)` where it
holds with equality form a facet of `STSP(n)`. -/
theorem theorem_5_1 (n : ℕ) (hn : 0 < n) (h4 : 4 ∣ n) :
    (∀ x ∈ STSP n, (n : ℝ) - 2 ≤ circletForm n x) ∧
      Disjunctive.Polarity.IsFacet (STSP n) (STSP n ∩ {x | circletForm n x = (n : ℝ) - 2}) := by sorry

end CircletTSP.Facet
