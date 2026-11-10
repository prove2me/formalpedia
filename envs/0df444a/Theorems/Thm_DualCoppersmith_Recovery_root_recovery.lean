-- Prove2me | Theorems.Thm_DualCoppersmith_Recovery_root_recovery
-- name    : DualCoppersmith.Recovery.root_recovery
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T02:56:28.084705+00:00
-- url     : https://prove2.me/theorems/e43f1c80-e177-48e6-b6f3-43ed99dacf16
-- title:
--   Theorem 3.4 — Root recovery
-- statement:
--   Let $(p,F,X)$ be a bounded modular root instance, let $r\in\mathbb Z^\ell$ be any target bounded root, and fix arbitrary integers $m,t\ge1$ with $t\ge\deg(f_a)$ for every relation. Let $n=|T_t|$, let $\rho=\operatorname{lcm}_{\alpha\in T_t}X^\alpha$, and use any certified LLL routine with valid factor $\delta\ge1$. If
--
--   $$\lambda_2(L_X^\perp)>\delta^{2(n-1)}\rho\sqrt n,$$
--
--   then Algorithm 2 on the input $(p,m,t,F,X)$ returns exactly $r$. Its conclusion is the equality of the full optional-output pipeline with success at $r$, including all integrality, strict-box and original-congruence checks.
--
--   The guarantee is deterministic and uses the actual second successive minimum. No Jacobian rank, coefficient-size restriction, product bound, root-uniqueness premise, or relation between $m$ and $t$ is added. The root is quantified only in the theorem; it is not supplied to the algorithm or the reduction contract. This is the paper’s complete main recovery claim.
--
--   Differences from the source:
--   - encoding: one-based variables and a fixed ordered monomial set → zero-based finite indices and a fixed equivalence enumerating all multi-indices of total degree at most t; reason: reindexing preserves every coordinate and uses the Euclidean norm
--   - encoding: degree is defined for nonzero polynomials although zero input relations are not excluded → zero relations have total degree zero and identically zero shift rows are omitted; reason: such rows impose only 0 = 0; every nonzero shift and every input instance is retained
--   - reading: root-Hermite factor δ, described in the introduction as a valid approximation factor → δ ≥ 1 with a certificate from adjacent Gram–Schmidt lengths or the routine’s external approximation law against every nonzero lattice vector; reason: the introduction, printed p. 1, specifies a valid factor; the external-law alternative retains every valid δ even when a Gram–Schmidt test is conservative, and no target-root property is certified
--   - encoding: the smallest radius containing the required independent lattice vectors → the infimum of nonnegative qualifying radii, with the published infimum-of-norms definition for λ₁; reason: full rank and discreteness ensure nonempty radius sets, boundedness below and attainment in every theorem use
--   - encoding: construct a modular kernel basis, reduce, and perform Algorithm 2’s tests → choose a basis of the explicit kernel if one exists, scale it, invoke the input-only routine, and return Option after exact rational tests; reason: the kernel contains p^m Z^n so a basis exists; the selection specification is only basis geometry and claims no runtime bound; the initial integral-coordinate guard always passes for this integral lattice
-- source:
--   Taehun Kang, Jebin Kim, Changmin Lee, JeongHwan Lee, STOC 2027 submission #1253 (October 2026), p. 9, Theorem 3.4 (PDF p. 10), proof through p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_DualCoppersmith_Recovery_Algorithm

set_option autoImplicit false

namespace DualCoppersmith.Recovery

/-- Theorem 3.4, printed p. 9 / PDF p. 10, proof through printed p. 10.
    The algorithm input and reduction certificate contain no hidden target root. -/
theorem root_recovery (I : Instance) (P : Parameters I)
    (delta : ℝ) (reduce : Reduction (dimension I P))
    (hreduce : ValidReduction I P delta reduce)
    (r : Fin I.ell → ℤ) (hr : IsBoundedRoot I r)
    (hgap : delta ^ (2 * (dimension I P - 1)) * (rho I P : ℝ) *
      Real.sqrt (dimension I P : ℝ) < secondMinimum (scaledLattice I P)) :
    algorithm2 I P reduce = some r := by sorry

end DualCoppersmith.Recovery
