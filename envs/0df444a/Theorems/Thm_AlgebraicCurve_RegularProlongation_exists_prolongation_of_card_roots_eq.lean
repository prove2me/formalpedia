-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq
-- name    : AlgebraicCurve.RegularProlongation.exists_prolongation_of_card_roots_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/ef241a9d-87fb-5f14-85f9-b6962cf9dc5a
-- title:
--   Kummer splitting of a regular prolongation in degree q
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, $F$ a field extension of $L$, and $\bar F$ (written `Fbar`) a field equipped with an algebra structure over the residue field of $A$. Let $R$ be a regular prolongation of $A$ to $F$ with values in $\bar F$: a valuation subring $\mathcal{O} = R.\mathrm{integers}$ of $F$ together with a ring homomorphism $R.\mathrm{residue} : \mathcal{O} \to \bar F$ such that an element $x \in L$ has $\mathrm{algebraMap}\,x \in \mathcal{O}$ exactly when $x \in A$, the residue map is surjective with kernel the maximal ideal of $\mathcal{O}$, it agrees on elements coming from $A$ with the residue map of $A$ followed by the structure map $\mathrm{ResidueField}(A) \to \bar F$, and every nonzero $g \in F$ can be scaled by some $c \in L$ so that $c \cdot g$ lies in $\mathcal{O}$ with nonzero residue. Let $q$ be a prime, let $f \in \mathcal{O}$, and let $S \subseteq \bar F$ be a finite set with exactly $q$ elements, each satisfying $s^q = R.\mathrm{residue}(f)$. Let $F'$ be a field extension of $F$, also an $L$-algebra compatibly with $F$, which is a splitting field over $F$ of $X^q - f$, and assume $[F' : F] = q$. Then there is a family $R' : \mathrm{Fin}\,q \to$ regular prolongations of $A$ to $F'$ with values in the same $\bar F$, such that the valuation subrings $(R'\,i).\mathrm{integers}$ are pairwise distinct, each contracts along $F \to F'$ to $\mathcal{O}$, and each residue map agrees with that of $R$ on elements of $(R'\,i).\mathrm{integers}$ coming from $\mathcal{O}$.
--
--   This is the valuation-theoretic form of Kummer's theorem in the unramified split case: when $X^q - \bar f$ has $q$ distinct roots in the residue field, the prolongation splits completely in the degree-$q$ Kummer extension $F(f^{1/q})$, with residue field and value group unchanged. It is used in the extraction of $q$-th roots from residues, namely by [`AlgebraicCurve.RegularProlongation.exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_isAlgClosed`](thm.html#AlgebraicCurve.RegularProlongation.exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_isAlgClosed) and [`AlgebraicCurve.RegularProlongation.exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one`](thm.html#AlgebraicCurve.RegularProlongation.exists_pow_eq_of_residue_eq_pow_of_finrank_eq_of_krullDimLE_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_prolongation_of_card_roots_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve Polynomial

theorem AlgebraicCurve.RegularProlongation.exists_prolongation_of_card_roots_eq
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    {q : ℕ} [Fact q.Prime] (f : R.integers)
    (S : Finset Fbar) (hS : S.card = q) (hSf : ∀ s ∈ S, s ^ q = R.residue f)
    (F' : Type*) [Field F'] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F']
    [IsSplittingField F F' (X ^ q - C (f : F))] (hdeg : Module.finrank F F' = q) :
    ∃ R' : Fin q → RegularProlongation A F' Fbar,
      Function.Injective (fun i => (R' i).integers) ∧
      ∀ i, (R' i).integers.comap (algebraMap F F') = R.integers ∧
        ∀ (x : (R' i).integers) (y : R.integers), algebraMap F F' y = x →
          (R' i).residue x = R.residue y := by sorry
