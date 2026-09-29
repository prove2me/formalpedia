-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_place_isRational_forall_mem_iff_exists_residue_eq_and_ord_eq_one_and_forall_eq_of_isNoetherianRing_range
-- name    : AlgebraicCurve.RegularProlongation.exists_place_isRational_forall_mem_iff_exists_residue_eq_and_ord_eq_one_and_forall_eq_of_isNoetherianRing_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/cc49e442-f9a0-5f0b-a417-c062a9b7ea4c
-- title:
--   Unique rational branch place with uniformiser ̄ y
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, $F$ a field extension of $L$ and $\bar F$ a field extension of the residue field $\kappa(A)$ of $A$, and let $R$ be a regular prolongation of $A$ to $F$ with values in $\bar F$: a valuation subring $R.\mathrm{integers}$ of $F$ whose intersection with $L$ is $A$, together with a surjective ring homomorphism $R.\mathrm{residue} : R.\mathrm{integers} \to \bar F$ whose kernel is the maximal ideal, compatible with the residue map of $A$ via $\kappa(A) \to \bar F$, and such that every non-zero $f \in F$ has an $L$-multiple lying in $R.\mathrm{integers}$ with non-zero residue. Let $\mathcal N$ be a subring of $F$ which is a local ring and is contained in $R.\mathrm{integers}$, such that the image of $A$ in $F$ lies in $\mathcal N$ and every $g \in \mathcal N$ differs from the image of some $a \in A$ by a non-unit of $\mathcal N$. Assume given $y \in \mathcal N$ which is not a unit and has non-zero residue, that every non-unit $f$ of $\mathcal N$ may be written $f = yg + h$ with $g,h \in \mathcal N$ and $R.\mathrm{residue}(h) = 0$, that the image subring $D := R.\mathrm{residue}(\mathcal N) \subseteq \bar F$ is Noetherian, and that every $z \in \bar F$ satisfies $z\,R.\mathrm{residue}(g) = R.\mathrm{residue}(f)$ for some $f,g \in \mathcal N$ with $R.\mathrm{residue}(g) \neq 0$. Then there is a place $x_1$ of $\bar F$ over $\kappa(A)$ — a valuation subring of $\bar F$, distinct from $\bar F$, containing the image of $\kappa(A)$ and a principal ideal ring — which is rational, in the sense that $\kappa(A) \to x_1.\mathrm{ResidueField}$ is surjective, and which satisfies: its valuation subring is exactly $D$; the residue of every non-unit of $\mathcal N$ is a non-unit of that valuation subring, and has strictly positive order $x_1.\mathrm{ord}$ when it is non-zero; $x_1.\mathrm{ord}(R.\mathrm{residue}(y)) = 1$; whenever $f \in \mathcal N$ and $a \in A$ are such that $f$ minus the image of $a$ is a non-unit of $\mathcal N$, the class of $R.\mathrm{residue}(f)$ in $x_1.\mathrm{ResidueField}$ is the image of the class of $a$ in $\kappa(A)$; and $x_1$ is the only place of $\bar F$ over $\kappa(A)$ whose valuation subring contains $R.\mathrm{residue}(\mathcal N)$.
--
--   This is the discrete-valuation-ring criterion that produces the branch places at an ordinary double point: the ring of reductions of a local subring along a branch is a discrete valuation ring with uniformiser the reduction of the node coordinate, and the associated place of the residue function field is rational and unique. It is used to supply the branch places, their uniqueness, and the evaluation of residues on constants in the analysis of nodes on modular curves, in particular for the Igusa ends of the full-level modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_place_isRational_forall_mem_iff_exists_residue_eq_and_ord_eq_one_and_forall_eq_of_isNoetherianRing_range.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.RegularProlongation.exists_place_isRational_forall_mem_iff_exists_residue_eq_and_ord_eq_one_and_forall_eq_of_isNoetherianRing_range
    {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (𝒩 : Subring F) [IsLocalRing ↥𝒩]
    (h𝒩 : ∀ f : F, f ∈ 𝒩 → f ∈ R.integers)

    (hA : ∀ a : ↥A, algebraMap L F (a : L) ∈ 𝒩)
    (hres : ∀ g : ↥𝒩, ∃ a : ↥A, ¬ IsUnit (g - ⟨algebraMap L F (a : L), hA a⟩))

    (y : ↥𝒩) (hyu : ¬ IsUnit y) (hy0 : R.residue ⟨(y : F), h𝒩 y y.2⟩ ≠ 0)

    (hmax : ∀ f : ↥𝒩, ¬ IsUnit f →
      ∃ g h : ↥𝒩, R.residue ⟨(h : F), h𝒩 h h.2⟩ = 0 ∧ f = y * g + h)

    (hnoeth : IsNoetherianRing
      ↥(R.residue.comp (Subring.inclusion (show 𝒩 ≤ R.integers.toSubring from fun f hf => h𝒩 f hf))).range)

    (hfrac : ∀ z : Fbar, ∃ f g : ↥𝒩, R.residue ⟨(g : F), h𝒩 g g.2⟩ ≠ 0 ∧
      z * R.residue ⟨(g : F), h𝒩 g g.2⟩ = R.residue ⟨(f : F), h𝒩 f f.2⟩) :
    ∃ x₁ : Place (ResidueField A) Fbar,
      x₁.IsRational ∧

      (∀ z : Fbar, z ∈ x₁.toValuationSubring ↔ ∃ f : ↥𝒩, R.residue ⟨(f : F), h𝒩 f f.2⟩ = z) ∧

      (∀ f : ↥𝒩, ¬ IsUnit f → R.residue ⟨(f : F), h𝒩 f f.2⟩ ∈ x₁.toValuationSubring.nonunits) ∧
      (∀ f : ↥𝒩, ¬ IsUnit f → R.residue ⟨(f : F), h𝒩 f f.2⟩ ≠ 0 →
        0 < x₁.ord (R.residue ⟨(f : F), h𝒩 f f.2⟩)) ∧

      x₁.ord (R.residue ⟨(y : F), h𝒩 y y.2⟩) = 1 ∧

      (∀ (f : ↥𝒩) (a : ↥A), ¬ IsUnit (f - ⟨algebraMap L F (a : L), hA a⟩) →
        ∀ m : R.residue ⟨(f : F), h𝒩 f f.2⟩ ∈ x₁.toValuationSubring,
          IsLocalRing.residue ↥x₁.toValuationSubring ⟨_, m⟩ =
            algebraMap (ResidueField A) x₁.ResidueField (IsLocalRing.residue ↥A a)) ∧

      (∀ Q' : Place (ResidueField A) Fbar,
        (∀ f : ↥𝒩, R.residue ⟨(f : F), h𝒩 f f.2⟩ ∈ Q'.toValuationSubring) → Q' = x₁) := by sorry
