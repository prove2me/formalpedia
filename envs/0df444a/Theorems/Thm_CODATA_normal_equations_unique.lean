-- Prove2me | Theorems.Thm_CODATA_normal_equations_unique
-- name    : CODATA.normal_equations_unique
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-21T15:49:17.415331+00:00
-- url     : https://prove2.me/theorems/b6f373f6-d009-4bd6-85ca-dc8d92c1c8d7
-- title:
--   The normal equations characterize the minimizers of the chi-square statistic
-- statement:
--   This is the characterization of the minimizers of a weighted least-squares adjustment by its normal equations, together with the uniqueness of the solution at full column rank, in the form used by the 2022 CODATA adjustment (section XII of the report).
--
--   Let $N$ input data $y \in \mathbb{R}^N$ be related to $M$ adjusted constants $x \in \mathbb{R}^M$ by the linear observational equations with design matrix $A \in \mathbb{R}^{N \times M}$ and offset $b \in \mathbb{R}^N$, so that the residual vector is $r(x) = y - (Ax + b)$. Let $G \in \mathbb{R}^{N \times N}$ be the weight matrix, assumed symmetric and strictly positive definite ($v^{\mathsf T} G v > 0$ for every $v \neq 0$), and let
--
--   $$
--   \chi^2(x) = r(x)^{\mathsf T} G\, r(x)
--   $$
--
--   be the chi-square statistic. A vector $x$ *solves the normal equations* when $A^{\mathsf T} G\, r(x) = 0$, that is, when every column of $A$ is $G$-orthogonal to the residual at $x$. Assume moreover that $A$ has full column rank, that is, $v \mapsto Av$ is injective. Then for every $x \in \mathbb{R}^M$:
--
--   1. $x$ minimizes $\chi^2$ over $\mathbb{R}^M$ if and only if $x$ solves the normal equations, and
--   2. any two solutions $z, w$ of the normal equations coincide:
--
--   $$
--   \bigl(\,\chi^2(x) = \min_{z} \chi^2(z) \iff A^{\mathsf T} G\, r(x) = 0\,\bigr) \quad\text{and}\quad \forall z, w:\; A^{\mathsf T} G\, r(z) = 0 \;\wedge\; A^{\mathsf T} G\, r(w) = 0 \implies z = w .
--   $$
--
--   This is the theorem that makes the CODATA adjustment procedure well defined: the adjusted constants of the 2022 report are determined as the solution of the normal equations, and by this equivalence they are exactly the minimizers of the chi-square statistic, uniquely so at full column rank.
--
--   **Formalization Note** The least-squares problem is the structure `LSQ N M` of the definition bundle, with `resid`, `chiSq`, `Minimizes`, `SolvesNormal` and `IsSPD` as above; full column rank is stated as injectivity of `L.A.mulVec`. This theorem replaces `CODATA.normal_equations`, whose uniqueness clause asserted $\forall z,\; A^{\mathsf T} G\, r(z) = 0 \implies z = x$ for an arbitrary $x$ without assuming that $x$ itself solves the normal equations, and was therefore false; only the uniqueness clause changes.
-- source:
--   P. J. Mohr, D. B. Newell, B. N. Taylor and E. Tiesinga, CODATA recommended values of the fundamental physical constants: 2022, J. Phys. Chem. Ref. Data 54, 033105 (2025), doi 10.1063/5.0279860; Rev. Mod. Phys. 97, 025002 (2025), doi 10.1103/RevModPhys.97.025002, section XII: the least-squares adjustment of the 133 input data for the 79 adjusted constants determines the adjusted constants by minimizing the chi-square statistic of the weighted residuals.

import Mathlib
import Definitions.Def_CODATA_lsa
import Definitions.Def_CODATA_uncert
import Definitions.Def_CODATA_values

/-!
# The normal equations characterize the minimizers

Section XII of the 2022 CODATA report describes the determination of
the recommended values as a least-squares adjustment: the adjusted
constants are chosen to minimize the chi-square statistic of the
weighted residuals. This milestone proves the classical equivalence
for the weighted model of `Def_CODATA_lsa`: when the weight matrix is
symmetric and strictly positive definite, the chi-square statistic is
a convex quadratic function of the adjusted constants, so its
minimizers are exactly the solutions of the normal equations; and when
the design matrix has full column rank, the solution of the normal
equations is unique. The milestone is proved on the way to the goal
theorem `CODATA.codata_self_consistent`. This statement replaces
`CODATA.normal_equations`, whose uniqueness clause quantified over an
arbitrary vector `x` without assuming that `x` solves the normal
equations; here uniqueness is stated as: any two solutions coincide.
-/

namespace CODATA

/-- For a least-squares problem whose weight matrix is symmetric and
strictly positive definite, the minimizers of the chi-square statistic
are exactly the solutions of the normal equations; and if the design
matrix has full column rank, then any two solutions of the normal
equations coincide. -/
theorem normal_equations_unique {N M : ℕ} (L : LSQ N M) (hG : IsSPD L.G)
    (hA : Function.Injective L.A.mulVec) (x : Fin M → ℝ) :
    (Minimizes L x ↔ SolvesNormal L x) ∧
      ∀ z w, SolvesNormal L z → SolvesNormal L w → z = w := by
  sorry

end CODATA
