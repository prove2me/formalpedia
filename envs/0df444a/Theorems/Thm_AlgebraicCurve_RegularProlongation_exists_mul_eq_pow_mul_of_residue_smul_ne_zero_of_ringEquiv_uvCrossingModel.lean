-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_mul_eq_pow_mul_of_residue_smul_ne_zero_of_ringEquiv_uvCrossingModel
-- name    : AlgebraicCurve.RegularProlongation.exists_mul_eq_pow_mul_of_residue_smul_ne_zero_of_ringEquiv_uvCrossingModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/cab4100a-6640-5034-89a0-9fabb7e662d5
-- title:
--   Factoring a unit-normalised element by a power of varpi
-- statement:
--   Let $L$ be a field, $A\subseteq L$ a valuation subring, $F$ a field extension of $L$ and $\bar F$ a field extension of the residue field of $A$, and let $R$ be a regular prolongation of $A$ to $F$ with values in $\bar F$: a valuation subring $R.\mathrm{integers}\subseteq F$ together with a surjective ring homomorphism $R.\mathrm{residue}$ from it to $\bar F$ whose kernel is the maximal ideal, such that an element of $L$ maps into $R.\mathrm{integers}$ exactly when it lies in $A$, the residue map agrees on constants with the residue map of $A$ followed by $\mathrm{ResidueField}\,A\to\bar F$, and every non-zero $f\in F$ has a scalar $c\in L$ with $c\cdot f$ in $R.\mathrm{integers}$ of non-zero residue. Let $\mathcal N_0\subseteq F$ be a Noetherian local subring contained in $R.\mathrm{integers}$. Let $\varpi\in L$ be non-zero, lie in $A$ with residue $0$ there, and have its image in $F$ inside $\mathcal N_0$. Let $W$ be a complete discrete valuation domain (adically complete for its maximal ideal), $\pi\in W$ irreducible, $E\ge 1$, and let $\iota$ be a ring isomorphism from the $\mathrm{maximalIdeal}\,\mathcal N_0$-adic completion of $\mathcal N_0$ onto $\mathrm{MvPowerSeries}(\mathrm{Fin}\,2)\,W/(X_0X_1-\pi^E)$ carrying the image of $\varpi$ to the class of the constant $\pi$. Assume given $p,s\in\mathcal N_0$ with $p\neq 0$ and $R.\mathrm{residue}\,p=0$, and with $R.\mathrm{residue}\,s\neq 0$ while $s$ is not a unit of $\mathcal N_0$. Then for all $a\in\mathcal N_0$ and $e\in L$ with $e\cdot a\in R.\mathrm{integers}$ of non-zero residue, there are $g\in\mathbb N$ and $a_1,a_2\in\mathcal N_0$ of non-zero residue with $a\,a_2=\varpi^{g}a_1$ in $\mathcal N_0$, and $e\varpi^{g}$ lies in $A$ and is a unit there.
--
--   This is the valuation-theoretic content behind the claim that the centre of the prolonged valuation ring on $\mathcal N_0$ is a height-one prime whose localisation is a discrete valuation ring with uniformiser $\varpi$: an element of $\mathcal N_0$ that becomes a unit after scaling by a constant $e$ differs from a unit of that localisation by exactly the power of $\varpi$ matching $e$. It feeds the node-annulus computation [`AlgebraicCurve.NodeAnnulusEngine.residue_eq_zero_and_ord_residue_eq_and_ord_residue_smul_eq_neg_of_eq_mul_V_pow`](thm.html#AlgebraicCurve.NodeAnnulusEngine.residue_eq_zero_and_ord_residue_eq_and_ord_residue_smul_eq_neg_of_eq_mul_V_pow), and uses the normality of $\mathcal N_0$ coming from its normal-crossing completion together with faithful flatness of completion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_mul_eq_pow_mul_of_residue_smul_ne_zero_of_ringEquiv_uvCrossingModel.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.RegularProlongation.exists_mul_eq_pow_mul_of_residue_smul_ne_zero_of_ringEquiv_uvCrossingModel
    {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
    (h𝒩₀R : ∀ f : F, f ∈ 𝒩₀ → f ∈ R.integers)
    (ϖ : L) (hϖ0 : ϖ ≠ 0) (hϖA : ϖ ∈ A) (hϖm : IsLocalRing.residue ↥A ⟨ϖ, hϖA⟩ = 0)
    (hϖN : algebraMap L F ϖ ∈ 𝒩₀)
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hιϖ : ι (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F ϖ, hϖN⟩) = const (π ^ E) π)
    (p s : ↥𝒩₀) (hp0 : p ≠ 0) (hp : R.residue ⟨(p : F), h𝒩₀R p p.2⟩ = 0)
    (hs : R.residue ⟨(s : F), h𝒩₀R s s.2⟩ ≠ 0) (hsu : ¬ IsUnit s)
    (a : ↥𝒩₀) (e : L) (h : e • (a : F) ∈ R.integers) (hne : R.residue ⟨e • (a : F), h⟩ ≠ 0) :
    ∃ (g : ℕ) (a₁ a₂ : ↥𝒩₀),
      R.residue ⟨(a₁ : F), h𝒩₀R a₁ a₁.2⟩ ≠ 0 ∧ R.residue ⟨(a₂ : F), h𝒩₀R a₂ a₂.2⟩ ≠ 0 ∧
      a * a₂ = ⟨algebraMap L F ϖ, hϖN⟩ ^ g * a₁ ∧
      ∃ hu : e * ϖ ^ g ∈ A, IsUnit (⟨e * ϖ ^ g, hu⟩ : ↥A) := by sorry
