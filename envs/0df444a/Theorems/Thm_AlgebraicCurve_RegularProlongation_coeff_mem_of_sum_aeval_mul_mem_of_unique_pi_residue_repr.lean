-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_coeff_mem_of_sum_aeval_mul_mem_of_unique_pi_residue_repr
-- name    : AlgebraicCurve.RegularProlongation.coeff_mem_of_sum_aeval_mul_mem_of_unique_pi_residue_repr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/de1a9872-4c8e-5292-bc33-6e48fd28762f
-- title:
--   Integrality of coefficients from joint integrality of sum_τ r_τ(f)z_τ
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring, let $F$ be a field extension of $L$, and let $\iota$ be a nonempty finite index type with a family of fields $\bar F_i$, each an algebra over the residue field $k = \mathrm{ResidueField}\,A$ of the local ring $A$. For each $i$ let $R_i$ be a regular prolongation of $A$ to $F$ with values in $\bar F_i$, that is: a valuation subring $\mathcal O_i \subseteq F$ together with a ring homomorphism $\mathrm{res}_i \colon \mathcal O_i \to \bar F_i$ such that $\mathcal O_i \cap L = A$ (in the sense that $\mathrm{algebraMap}_{L,F}(x) \in \mathcal O_i$ iff $x \in A$), $\mathrm{res}_i$ is surjective with kernel the maximal ideal of $\mathcal O_i$, $\mathrm{res}_i$ restricted to $A$ is the residue map of $A$ followed by $k \to \bar F_i$, and every nonzero $f \in F$ admits $c \in L$ with $c \cdot f \in \mathcal O_i$ and $\mathrm{res}_i(c\cdot f) \neq 0$. Fix $f \in \bigcap_i \mathcal O_i$ and, for a natural number $d$, elements $z_\tau \in \bigcap_i \mathcal O_i$ indexed by $\tau \in \mathrm{Fin}\,d$. Assume the uniqueness hypothesis: any two families $q, q' \colon \mathrm{Fin}\,d \to k[X]$ with $\sum_\tau q_\tau(\mathrm{res}_i f)\,\mathrm{res}_i z_\tau = \sum_\tau q'_\tau(\mathrm{res}_i f)\,\mathrm{res}_i z_\tau$ for every $i$ are equal. Then for every family $r \colon \mathrm{Fin}\,d \to L[X]$ with $\sum_\tau r_\tau(f)\,z_\tau \in \mathcal O_i$ for all $i$, every coefficient of every $r_\tau$ lies in $A$.
--
--   This is the coefficient-integrality step in the classical theory of constant reduction of function fields: joint integrality of a combination $\sum_\tau r_\tau(f) z_\tau$ over all prolongations forces the polynomials $r_\tau$ to have coefficients in $A$, provided the corresponding residue representations are unique. It is used in the construction of reduced bases compatible with a family of prolongations, and is cited in the analysis of localisations of modular curves via [`ModularCurve.exists_mul_coeffMap_eq_iff_coe_mem_modularLocalized_of_not_dvd`](thm.html#ModularCurve.exists_mul_coeffMap_eq_iff_coe_mem_modularLocalized_of_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_coeff_mem_of_sum_aeval_mul_mem_of_unique_pi_residue_repr.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing Polynomial

theorem AlgebraicCurve.RegularProlongation.coeff_mem_of_sum_aeval_mul_mem_of_unique_pi_residue_repr
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] [Nonempty ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (d : ℕ) (z : Fin d → F) (hzO : ∀ τ i, z τ ∈ (R i).integers)
    (huniqres : ∀ q q' : Fin d → Polynomial (IsLocalRing.ResidueField A),
      (∀ i, ∑ τ, Polynomial.aeval ((R i).residue ⟨f, hf i⟩) (q τ)
          * (R i).residue ⟨z τ, hzO τ i⟩
        = ∑ τ, Polynomial.aeval ((R i).residue ⟨f, hf i⟩) (q' τ)
          * (R i).residue ⟨z τ, hzO τ i⟩) →
      q = q')
    (r : Fin d → Polynomial L)
    (hsum : ∀ i, ∑ τ, Polynomial.aeval f (r τ) * z τ ∈ (R i).integers) :
    ∀ τ j, (r τ).coeff j ∈ A := by sorry
