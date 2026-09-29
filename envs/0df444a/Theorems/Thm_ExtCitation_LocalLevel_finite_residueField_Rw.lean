-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_finite_residueField_Rw
-- name    : ExtCitation.LocalLevel.finite_residueField_Rw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/880117c7-fd94-5d85-9570-7a84dae11b90
-- title:
--   Finiteness of the residue field of R_w
-- statement:
--   Let $q$ be a prime number and let $K_w$ be an intermediate field of the extension $\overline{\mathbb{Q}}_q/\mathbb{Q}_q$, where $\overline{\mathbb{Q}}_q$ is the algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$, and assume $K_w$ is finite-dimensional over $\mathbb{Q}_q$. Write [`padicIntegers q`](def/GaloisRep_CompletionBridge.html#L20) for the valuation subring of $\overline{\mathbb{Q}}_q$ attached to its canonical $\mathbb{R}_{\ge 0}$-valued valuation `Valued.v`, i.e. the set of elements of absolute value at most $1$, and let $R_w =$ `Rw q Kw` be its preimage in $K_w$ under the structure map $K_w \to \overline{\mathbb{Q}}_q$, a valuation subring of $K_w$. The assertion is that the residue field of the local ring $R_w$, that is the quotient of $R_w$ by its maximal ideal, is a finite type. No bound on the cardinality, and no identification of the residue field with a specific finite field, is asserted.
--
--   This is the standard fact that the ring of integers of a finite extension $K_w$ of $\mathbb{Q}_q$ inside $\overline{\mathbb{Q}}_q$ has finite residue field. It underlies the local analysis at the auxiliary primes $w$, being used for instance in the statements about $q$-power-Frobenius behaviour of roots of minimal polynomials over $R_w$ and in the comparison of unramified levels by index.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_finite_residueField_Rw.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.finite_residueField_Rw (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] :
    Finite (IsLocalRing.ResidueField (Rw q Kw)) := by sorry
