-- Prove2me | Theorems.Thm_AlgebraicCurve_mem_localRing_of_mem_integers_of_forall_mem_valuationSubring_of_mem_smoothLocus
-- name    : AlgebraicCurve.mem_localRing_of_mem_integers_of_forall_mem_valuationSubring_of_mem_smoothLocus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/ec90a038-3e8a-5d18-865d-67bf9f750bf6
-- title:
--   Locality of the local ring at a smooth special point
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring which is henselian as a local ring, is not all of $L$, and satisfies the rank condition that for all $a, b \in A$ with $a$ in the maximal ideal and $b \neq 0$ there is $n$ with $b \mid a^{n}$. Let $F$ be a field extension of $L$ which is `IsCurveOver L F` (every nonzero element of $F$ has a degree-zero divisor recording its orders at all places, every place of $F/L$ has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$) and essentially of finite type over $L$. Let $X$ be an integral scheme with a proper, flat, locally finitely presented morphism `toBase` to $\operatorname{Spec} A$, and $\varphi : F \cong K(X)$ a ring isomorphism carrying $\mathrm{image}(A \to L \to F)$ to the structural map $A \to K(X)$ induced by `toBase`. Let $x \in X$ lie over the closed point of $A$, be maximal for specialisation ($x \rightsquigarrow y$ implies $y = x$) and lie in the smooth locus of `toBase`, and let $\eta \neq x$ also lie over the closed point with $\eta \rightsquigarrow x$. Let $Fbar$ be a field over the residue field of $A$ and $R$ a `RegularProlongation` of $A$ to $F$ with values in $Fbar$: a valuation subring $R.\mathrm{integers}$ of $F$ with a surjective residue homomorphism onto $Fbar$ whose kernel is the maximal ideal, whose intersection with $L$ is exactly $A$ compatibly with residues, and such that every nonzero $f \in F$ has an $L$-multiple lying in $R.\mathrm{integers}$ with nonzero residue; assume $R.\mathrm{integers}$, as a subring of $F$, equals the image $\varphi^{-1}(\mathcal{O}_{X,\eta}) \subseteq F$. Put $S := \varphi^{-1}(\mathcal{O}_{X,x}) \subseteq F$. Then for every $f \in R.\mathrm{integers}$: if $f$ lies in the valuation subring of every place $P$ of $F/L$ (a valuation subring of $F$, proper, containing $L$, and a principal ideal ring) which is centred at $x$ in the sense that every $g \in S$ lies in $P$'s valuation subring with $P.\mathrm{evalAt}\,g \in A$ and $P.\mathrm{evalAt}\,g$ a unit of $A$ exactly when $g$ is invertible in $S$, then $f \in S$.
--
--   This is the locality statement for the local ring at a smooth point of the special fibre: a function integral along the component through $\eta$ and without poles on the residue disc of $x$ (the places centred at $x$) is regular at $x$, which expresses $\mathcal{O}_{X,x}$ as the intersection of the vertical localisation $R.\mathrm{integers}$ with the valuation rings of the horizontal places. It feeds the construction of the smooth-point ring with its membership criterion, locality and residue surjectivity, and the vanishing-of-order statement used in the descent to a discrete valuation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_mem_localRing_of_mem_integers_of_forall_mem_valuationSubring_of_mem_smoothLocus.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.mem_localRing_of_mem_integers_of_forall_mem_valuationSubring_of_mem_smoothLocus
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
    (R : RegularProlongation A F Fbar)
    (hR : R.integers.toSubring = SemistableModel.localRing X φ η) :
    let S : Subring F := SemistableModel.localRing X φ x
    ∀ f : F, f ∈ R.integers →
      (∀ P : Place L F,
        (∀ g : F, g ∈ S → g ∈ P.toValuationSubring ∧ ∃ h : P.evalAt g ∈ A,
          (IsUnit (⟨P.evalAt g, h⟩ : ↥A) ↔ ∃ g' ∈ S, g * g' = 1)) →
        f ∈ P.toValuationSubring) →
      f ∈ S := by sorry
