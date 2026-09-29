-- Prove2me | Theorems.Thm_ExtCitation_LocalLevel_aeval_pow_card_residueField_minpoly_eq_zero
-- name    : ExtCitation.LocalLevel.aeval_pow_card_residueField_minpoly_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/126482a9-52e6-5e9f-b0bd-2140860338e9
-- title:
--   ζ₀^{q^a} is a K-conjugate of ζ₀
-- statement:
--   Fix a prime $q$ and let $K$ be an intermediate field of the extension $\overline{\mathbb{Q}}_q/\mathbb{Q}_q$ (the algebraic closure being the project's model `PadicAlgCl q`) which is finite-dimensional over $\mathbb{Q}_q$. Write $R_K$ for `Rw q K`, the valuation subring of $K$ obtained by pulling back, along the structure map $K \to \overline{\mathbb{Q}}_q$, the valuation subring of the canonical rank-one valuation on $\overline{\mathbb{Q}}_q$; thus $R_K$ is the ring of integers of $K$, and `IsLocalRing.ResidueField (Rw q K)` is its residue field. Let $m$ be a natural number not divisible by $q$ and let $\zeta_0 \in \overline{\mathbb{Q}}_q$ be a primitive $m$-th root of unity. The assertion is that there exists a natural number $a$ with $a > 0$ such that the residue field of $R_K$ has cardinality exactly $q^a$ and such that $\zeta_0^{q^a}$ is a root of the minimal polynomial of $\zeta_0$ over $K$, i.e. the evaluation of $\mathrm{minpoly}_K(\zeta_0) \in K[X]$ at $\zeta_0^{q^a}$, taken in $\overline{\mathbb{Q}}_q$ via the algebra structure, vanishes.
--
--   This is the arithmetic half of the statement that raising to the power of the residue cardinality acts on $m$-th roots of unity ($q \nmid m$) as an element of the Galois group of $K(\zeta_0)/K$: it produces the residue degree $a$ together with the conjugacy of $\zeta_0^{q^a}$ with $\zeta_0$ over $K$. It feeds the construction of a Frobenius element for $K(\zeta_0)/K$ in [`IntermediateField.exists_frobenius_adjoin_rootsOfUnity_padic`](thm.html#IntermediateField.exists_frobenius_adjoin_rootsOfUnity_padic), and through it the local construction of cocycles attached to cyclotomic characters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ExtCitation_LocalLevel_aeval_pow_card_residueField_minpoly_eq_zero.lean

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open IntermediateField ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.aeval_pow_card_residueField_minpoly_eq_zero (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (m : ℕ) (hm : ¬ q ∣ m)
    (ζ₀ : PadicAlgCl q) (hζ₀ : IsPrimitiveRoot ζ₀ m) :
    ∃ a : ℕ, 0 < a ∧ Nat.card (IsLocalRing.ResidueField (Rw q K)) = q ^ a ∧
      Polynomial.aeval (ζ₀ ^ (q ^ a)) (minpoly K ζ₀) = 0 := by sorry
