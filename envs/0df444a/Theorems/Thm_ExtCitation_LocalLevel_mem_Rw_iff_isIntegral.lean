-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_mem_Rw_iff_isIntegral
-- name    : ExtCitation.LocalLevel.mem_Rw_iff_isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/f7f296a2-fc28-5270-9bae-f69b6a6188bb
-- title:
--   Unit ball of a finite level equals integral closure of ℤ_q
-- statement:
--   Let $q$ be a prime and let $K_w$ be an intermediate field of the extension $\overline{\mathbb{Q}}_q/\mathbb{Q}_q$, where $\overline{\mathbb{Q}}_q$ is `PadicAlgCl q`, assumed finite-dimensional over $\mathbb{Q}_q$. Here [`padicIntegers q`](def/GaloisRep_CompletionBridge.html#L20) denotes the valuation subring of $\overline{\mathbb{Q}}_q$ attached to its $\mathbb{R}_{\ge 0}$-valued valuation `Valued.v`, that is $\{y : v(y) \le 1\}$, and `Rw q Kw` is its preimage under the structure map $K_w \to \overline{\mathbb{Q}}_q$, regarded as a valuation subring of $K_w$. The assertion is that for every $x \in K_w$, the element $x$ lies in `Rw q Kw` — equivalently, the valuation of the image of $x$ in $\overline{\mathbb{Q}}_q$ is at most $1$ — if and only if that image is integral over $\mathbb{Z}_q$, i.e. is a root of a monic polynomial with coefficients in the $q$-adic integers. Thus the closed unit ball of a finite level is exactly the integral closure of $\mathbb{Z}_q$ in it.
--
--   This identifies the valuation subring $R_w$ of a finite extension $K_w/\mathbb{Q}_q$ inside $\overline{\mathbb{Q}}_q$ with the integral closure of $\mathbb{Z}_q$, so that the general theory of integral closures in finite extensions of complete discretely valued fields (finiteness, discreteness of the valuation, completeness of the maximal-ideal adic topology) applies to $R_w$. It is used in the local-level constructions, for instance in producing normal-basis lattices, in clearing denominators of linearly independent families by powers of a uniformiser, and in the computation of ramification indices for $R_w$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_mem_Rw_iff_isIntegral.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.mem_Rw_iff_isIntegral (q : ℕ) [Fact q.Prime]
    (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw] (x : Kw) :
    x ∈ Rw q Kw ↔ IsIntegral ℤ_[q] (x : PadicAlgCl q) := by sorry
