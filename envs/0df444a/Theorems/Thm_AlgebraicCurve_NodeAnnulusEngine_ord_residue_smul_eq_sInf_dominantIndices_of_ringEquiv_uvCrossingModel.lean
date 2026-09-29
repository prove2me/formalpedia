-- Prove2me | Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel
-- name    : AlgebraicCurve.NodeAnnulusEngine.ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/9f1e6a88-ab75-5dc7-8145-ae5d7e3278ee
-- title:
--   Order at the U-end as least dominant index
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A$ a valuation subring of $L$, and $F$ a field extension of $L$ which is a curve over $L$ (principal divisors, residue fields of places finite over $L$, and $\Omega_{F/L}$ free of rank one) and essentially of finite type over $L$. Let $\mathrm{Fbar}_1,\mathrm{Fbar}_2$ be fields over the residue field $\kappa$ of $A$, and $R_1,R_2$ regular prolongations of $A$ to $F$ with these residue fields: each consists of a valuation subring $R_i.\mathrm{integers}$ of $F$ together with a surjective residue homomorphism onto $\mathrm{Fbar}_i$ whose kernel is the maximal ideal, with $\mathrm{algebraMap}\,x \in R_i.\mathrm{integers}$ exactly for $x\in A$, compatibility of residues with $\kappa\to\mathrm{Fbar}_i$, and the property that every nonzero $f\in F$ has $c\cdot f$ in the ring with nonzero residue for some $c\in L$. Let $x_1,x_2$ be places of $\mathrm{Fbar}_i$ over $\kappa$, and $S$ a set of places of $F/L$, all rational. Let $\mathcal N_0\subseteq F$ be a Noetherian local subring contained in both $R_1.\mathrm{integers}$ and $R_2.\mathrm{integers}$, such that $S$ consists precisely of the places whose valuation subring contains $\mathcal N_0$ and at which every non-unit of $\mathcal N_0$ evaluates into the maximal ideal of $A$; assume every $f\in F$ satisfies $f\,b=\sum_i c_i a_i$ for some nonzero $b\in\mathcal N_0$, finitely many $a_i\in\mathcal N_0$ and $c_i\in L$. Let $C\subseteq A$ be a subring of constants whose image lies in $\mathcal N_0$, a domain and a discrete valuation ring, with $\varpi\in C$ nonzero such that the residue of $d\in C$ in $\kappa$ vanishes exactly when $\varpi\mid d$ in $C$; assume every element of $A$ is algebraic over $C$, that families in $L$ linearly independent over $C$ remain independent for $\mathcal N_0$-coefficient relations, that for $a$ in the maximal ideal of $A$ and $b\neq0$ in $A$ some power $a^n$ is divisible by $b$, and that every $g\in\mathcal N_0$ becomes a non-unit after subtracting some constant from $C$. Let $W$ be a complete discrete valuation domain, $\pi\in W$ irreducible, $\sigma:W\to\widehat{\mathcal N_0}$ a ring homomorphism with $\sigma(\pi)$ the image of $\varpi$, $E\geq1$, and $\iota:\widehat{\mathcal N_0}\xrightarrow{\ \sim\ }\mathrm{MvPowerSeries}(\mathrm{Fin}\,2,W)/\mathrm{uvCrossingIdeal}(W,\pi^E)$ a ring isomorphism carrying $\sigma(o)$ to the constant $o$. Assume the two end laws: if $f\in\mathcal N_0$ has nonzero $R_1$-residue of order $n$ at $x_1$ then $\iota(f)-\gamma V^n\in(\pi,U)$ for some unit $\gamma$, and symmetrically $\iota(f)-\gamma U^n\in(\pi,V)$ for the $R_2$-residue and $x_2$. Assume further node coordinates $x,y\in\mathcal N_0$ with $R_1$-residue of $x$ zero and $\mathrm{ord}_{x_2}$ of its $R_2$-residue equal to $1$, and $R_2$-residue of $y$ zero with $\mathrm{ord}_{x_1}$ of its $R_1$-residue equal to $1$. Finally let $q\geq1$, $a\in\mathcal N_0$, $e\in L$ with $e\cdot a\in R_2.\mathrm{integers}$ of nonzero $R_2$-residue, and let $(\alpha,\beta)$ be a pair of power series over $W$ with $\beta(0)=0$ representing $\iota(a)$ as $\mathrm{inU}\,\alpha+\mathrm{inV}\,\beta$ in the quotient. Then $\mathrm{ord}_{x_2}$ of the $R_2$-residue of $e\cdot a$ equals the infimum of the set of dominant indices of $(\alpha,\beta)$ for the scaled valuation $w\mapsto q\cdot\mathrm{addVal}_W(w)$ with parameters $qE$ and $0$, i.e. of the indices at which the term order agrees with the Gauss order of the representative $\mathrm{inU}\,\alpha+\mathrm{inV}\,\beta$.
--
--   This is the end reader at the $U$-branch of the node–annulus dictionary: it converts the order of vanishing at the place $x_2$ of the second residue curve, after normalisation by a constant $e\in L$ allowing $a$ to vanish at the first end, into the least dominant index of the normal form of $a$ in the crossing model $W[[U,V]]/(UV-\pi^E)$. It feeds the layerwise statement [`AlgebraicCurve.NodeAnnulusEngine.ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers`](thm.html#AlgebraicCurve.NodeAnnulusEngine.ord_residue_nonneg_and_finsum_ord_eq_ord_residue_add_of_ringEquiv_uvCrossingModel_layers), and rests on [`ModularCurve.UVCrossingModel.sInf_dominantIndices_eq_of_sub_mul_U_pow_mem`](thm.html#ModularCurve.UVCrossingModel.sInf_dominantIndices_eq_of_sub_mul_U_pow_mem) together with the multiplicativity and scaling properties of dominant indices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.NodeAnnulusEngine.ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    {Fbar₁ : Type*} [Field Fbar₁] [Algebra (ResidueField A) Fbar₁]
    {Fbar₂ : Type*} [Field Fbar₂] [Algebra (ResidueField A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (x₁ : Place (ResidueField A) Fbar₁) (x₂ : Place (ResidueField A) Fbar₂)
    (S : Set (Place L F))
    (hrat : ∀ P ∈ S, P.IsRational)
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
    (h𝒩₀R : ∀ f : F, f ∈ 𝒩₀ → f ∈ R₁.integers ∧ f ∈ R₂.integers)
    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))
    (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F))
    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ((ϖ : ↥C) : L) ≠ 0)
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C a)
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0 → ∀ i, a i = 0)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hres : ∀ g : ↥𝒩₀, ∃ o : ↥C, ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩))
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
    (hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (hres₁ : ∀ (f : ↥𝒩₀) (n : ℕ), R₁.residue ⟨f, (h𝒩₀R f f.2).1⟩ ≠ 0 →
      x₁.ord (R₁.residue ⟨f, (h𝒩₀R f f.2).1⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap ↥𝒩₀ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hres₂ : ∀ (f : ↥𝒩₀) (n : ℕ), R₂.residue ⟨f, (h𝒩₀R f f.2).2⟩ ≠ 0 →
      x₂.ord (R₂.residue ⟨f, (h𝒩₀R f f.2).2⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap ↥𝒩₀ _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (x y : F) (hxmem : x ∈ 𝒩₀) (hymem : y ∈ 𝒩₀)
    (x_fst : R₁.residue ⟨x, (h𝒩₀R x hxmem).1⟩ = 0)
    (x_snd : x₂.ord (R₂.residue ⟨x, (h𝒩₀R x hxmem).2⟩) = 1)
    (y_snd : R₂.residue ⟨y, (h𝒩₀R y hymem).2⟩ = 0)
    (y_fst : x₁.ord (R₁.residue ⟨y, (h𝒩₀R y hymem).1⟩) = 1)
    (q : ℕ) (hq : 1 ≤ q)
    (a : ↥𝒩₀) (e : L) (h : e • (a : F) ∈ R₂.integers) (hne : R₂.residue ⟨e • (a : F), h⟩ ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (π ^ E) (inU ab.1 + inV ab.2) = ι (algebraMap ↥𝒩₀ _ a)) :
    x₂.ord (R₂.residue ⟨e • (a : F), h⟩) =
      sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * E) 0 ab) := by sorry
