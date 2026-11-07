-- Prove2me | Theorems.Thm_FixpReciprocal_theorem_1_1
-- name    : FixpReciprocal.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:52:55.099201+00:00
-- url     : https://prove2.me/theorems/850adfd8-9033-4135-bf17-fa75e94b452f
-- title:
--   Theorem 1.1 (= Theorem 4.2) — exact generalized circuits with clipped affine and reciprocal gates are FIXP-complete
-- statement:
--   Fix a rational $\tau>0$. An instance is a system of one equation for each of $N\ge1$ variables $x_1,\dots,x_N\in[0,1]$, each of the form
--   $$x_i=[\![a_ix_{j_i}+b_ix_{k_i}+c_i]\!]\qquad\text{or}\qquad x_i=\frac{1}{1+\tau x_{j_i}},$$
--   with binary-encoded rational coefficients, input indices in $[N]$, and cycles allowed.
--
--   Finding an exact solution is FIXP-complete: the problem belongs to FIXP, and every problem in FIXP admits an SL-reduction to it.
--
--   This lets exact hardness reductions avoid implementing multiplication or squaring. The paper's three auction applications are derived from it.
--
--   Differences from the source:
--
--   - reading: "We therefore assume that input circuits contain at least one nonconstant gate" (p.11), a remark or part of the problem → both: completeness of reciprocalProblem and of reciprocalProblemNC, as a conjunction; reason: the sentence is ambiguous and neither reading is stronger, since restricting instances makes membership easier and hardness harder
--   - reading: polynomial time → Mathlib's Turing.TM2ComputableInPolyTime over fixed binary encodings in the alphabet Sym; reason: the paper names no machine model; §3, p.10 measures input size by bit length
--   - encoding: a constant or unary gate of A → aff with zero coefficients and valid dummy indices; reason: "Arguments with zero coefficients may be omitted" (p.11)
--   - encoding: 0-based indices, instances as subtypes, the list-of-triples recovery data → the corresponding Lean data; reason: same instances and reductions; see the definitions' notes
--   - encoding: an algebraic circuit as a finite directed acyclic circuit → a straight-line program, each operation reading earlier wires; reason: a topological order of the DAG; same maps
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), Theorem 1.1, p.2 (PDF p.4); Theorem 4.2, p.12 (PDF p.14)

import Mathlib
import Definitions.Def_FixpReciprocal_FIXPComplete
import Definitions.Def_FixpReciprocal_reciprocalProblem

namespace FixpReciprocal

/-- **Theorem 1.1 (= Theorem 4.2, completeness with reciprocal gates).** For every fixed rational `τ > 0`, finding an
exact solution of a generalized circuit using only the gates in (1) is FIXP-complete.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), Theorem 1.1, p.2; Theorem 4.2, p.12.

**Formalization Note.** Stated for all valid circuits and for the circuits with a nonconstant gate, the
two readings of "We therefore assume that input circuits contain at least one nonconstant gate" (p.11). Machines
may depend on `τ`. -/
theorem theorem_1_1 (τ : ℚ) (hτ : 0 < τ) :
    FIXPComplete (reciprocalProblem τ) ∧ FIXPComplete (reciprocalProblemNC τ) := by sorry

end FixpReciprocal
