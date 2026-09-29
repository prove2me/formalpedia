-- Prove2me | Theorems.Thm_AlgebraicCurve_existsUnique_place_residue_localRing_surjective_of_mem_smoothLocus_of_valuationSubring
-- name    : AlgebraicCurve.existsUnique_place_residue_localRing_surjective_of_mem_smoothLocus_of_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/f64d9fdb-b914-5094-978e-d3ddce68f427
-- title:
--   Reduction of a smooth special point is a place
-- statement:
--   Let $L$ be an algebraically closed field and $A$ a valuation subring of $L$ satisfying: for all $a,b\in A$ with $a$ in the maximal ideal and $b\neq 0$ there is $n$ with $b\mid a^{n}$; $A\neq L$; and $A$ henselian local. Let $F$ be a field with an $L$-algebra structure which is essentially of finite type and satisfies `IsCurveOver L F`, i.e. every nonzero $f\in F$ has a degree-zero divisor whose value at each place $v$ is $v.\mathrm{ord}\,f$, every place has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank $1$ over $F$. Let $X$ be an integral scheme with a proper, flat, locally finitely presented morphism `toBase` to $\operatorname{Spec}A$, and $\varphi\colon F\cong K(X)$ a ring isomorphism carrying each $a\in A$ (viewed in $F$) to its image under `SemistableModel.baseToFunctionField toBase`. Let $x\in X$ lie over the closed point of $A$, be closed (any $y$ with $x\rightsquigarrow y$ equals $x$) and lie in the smooth locus of `toBase`, and let $\eta\neq x$ lie over the closed point with $\eta\rightsquigarrow x$. Let $\bar F$ be a field over the residue field $\kappa$ of $A$, and $\mathcal O$ a valuation subring of $F$ equipped with a surjective ring homomorphism $\mathrm{res}\colon\mathcal O\to\bar F$ whose kernel is the maximal ideal of $\mathcal O$ and which sends each constant $a\in A\cap\mathcal O$ to the image of its residue in $\bar F$; assume $\mathcal O$ coincides, as a subring of $F$, with `SemistableModel.localRing X φ η`, the image in $F$ of the stalk of $X$ at $\eta$. Put $S:=$ `SemistableModel.localRing X φ x`, the image in $F$ of the stalk at $x$. Then $S\subseteq\mathcal O$, and there is a place $Q$ of $\bar F$ over $\kappa$ (a valuation subring containing the image of $\kappa$, not all of $\bar F$, and a principal ideal ring) such that $Q$ is rational ($\kappa$ surjects onto its residue field), $\mathrm{res}$ maps $S$ into $\mathcal O_Q$ and onto $\mathcal O_Q$ (every $g\in\mathcal O_Q$ is $\mathrm{res}\,f$ for some $f\in S\cap\mathcal O$), an element $f\in S$ is a unit of $S$ precisely when $\mathrm{res}\,f\neq 0$ and $Q.\mathrm{ord}(\mathrm{res}\,f)=0$, some $T\in S$ has $Q.\mathrm{ord}(\mathrm{res}\,T)=1$, and $Q$ is the only place of $\bar F$ over $\kappa$ with $\mathrm{res}(S)\subseteq\mathcal O_{Q}$.
--
--   This is the statement that the reduction of a smooth closed point of the special fibre of a model over a henselian valuation ring is a rational place of the residue function field, in the form where the prolongation along the adjacent point $\eta$ is given by a bare reduction datum (a valuation subring of $F$ with a surjective residue map onto $\bar F$ having the maximal ideal as kernel and compatible with constants), rather than by a regular local ring with ramification index one. It feeds the computation of orders of reductions on models of relative dimension one, via [`AlgebraicCurve.ord_residue_eq_zero_of_forall_ord_eq_zero_of_smoothOfRelativeDimension_one_dvrDescent_of_exists_smul_mem`](thm.html#AlgebraicCurve.ord_residue_eq_zero_of_forall_ord_eq_zero_of_smoothOfRelativeDimension_one_dvrDescent_of_exists_smul_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_existsUnique_place_residue_localRing_surjective_of_mem_smoothLocus_of_valuationSubring.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.existsUnique_place_residue_localRing_surjective_of_mem_smoothLocus_of_valuationSubring
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    [HenselianLocalRing ↥A]
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x) (hxs : x ∈ toBase.smoothLocus)
    (η : X) (hηx : η ⤳ x) (hne : η ≠ x) (hη : toBase.base η = closedPoint ↥A)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (𝒪 : ValuationSubring F) (resd : ↥𝒪 →+* Fbar) (hsurj : Function.Surjective resd)
    (hker : RingHom.ker resd = maximalIdeal ↥𝒪)
    (hcompat : ∀ (a : ↥A) (h : algebraMap L F (a : L) ∈ 𝒪),
      resd ⟨algebraMap L F (a : L), h⟩ = algebraMap (ResidueField ↥A) Fbar (IsLocalRing.residue ↥A a))
    (h𝒪 : 𝒪.toSubring = SemistableModel.localRing X φ η) :
    let S : Subring F := SemistableModel.localRing X φ x
    (∀ f : ↥S, (f : F) ∈ 𝒪) ∧
    ∃ Q : Place (ResidueField ↥A) Fbar,
      Q.IsRational ∧
      (∀ f : ↥S, ∃ hR : (f : F) ∈ 𝒪, resd ⟨(f : F), hR⟩ ∈ Q.toValuationSubring) ∧
      (∀ g : Fbar, g ∈ Q.toValuationSubring →
        ∃ (f : F) (hf : f ∈ 𝒪), f ∈ S ∧ resd ⟨f, hf⟩ = g) ∧
      (∀ (f : ↥S) (hR : (f : F) ∈ 𝒪),
        IsUnit f ↔ Q.ord (resd ⟨(f : F), hR⟩) = 0 ∧ resd ⟨(f : F), hR⟩ ≠ 0) ∧
      (∃ (T : ↥S) (hR : (T : F) ∈ 𝒪), Q.ord (resd ⟨(T : F), hR⟩) = 1) ∧
      (∀ Q' : Place (ResidueField ↥A) Fbar,
        (∀ f : ↥S, ∃ hR : (f : F) ∈ 𝒪, resd ⟨(f : F), hR⟩ ∈ Q'.toValuationSubring) → Q' = Q) := by sorry
