-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_exists_mem_integers_residue_uniqueRepr_and_span
-- name    : AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_forall_exists_mem_integers_residue_uniqueRepr_and_span
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/686ce43e-8adf-5fa8-bfda-c5c58e5facde
-- title:
--   Reduction of an integral basis at almost all constant places
-- statement:
--   Let $L$ be an algebraically closed field, $F$ a field extension of $L$, and $f \in F$ such that $F$ is finite-dimensional and separable over the intermediate field $L(f) = L(\{f\})$. Let $\iota$ be a finite index type and $y \colon \iota \to F$ a family with $\#\iota = [F : L(f)]$ such that (i) each $y_i$ lies in every valuation subring $V$ of $F$ that contains the image of $L$ and contains $f$, and (ii) whenever $c \colon \iota \to L[X]$ satisfies $\sum_i c_i(f)\,y_i = 0$, all $c_i$ vanish. Then there is a finite set $S \subseteq L$ of nonzero elements such that for every valuation subring $A$ of $L$ with $\mathrm{val}_A(s) = 1$ for all $s \in S$, every field $F_b$ that is an algebra over the residue field $\kappa = \kappa(A)$, and every regular prolongation $R$ of $A$ to $F$ with values in $F_b$ — that is, a valuation subring $R.\mathrm{integers} \subseteq F$ with $\mathrm{algebraMap}(x) \in R.\mathrm{integers} \iff x \in A$ for $x \in L$, together with a surjective ring homomorphism $R.\mathrm{residue} \colon R.\mathrm{integers} \to F_b$ whose kernel is the maximal ideal, which is compatible with the residue map of $A$ over $\kappa \to F_b$, and such that every nonzero element of $F$ becomes, after scaling by a constant, an element of $R.\mathrm{integers}$ with nonzero residue — the following holds: if $f \in R.\mathrm{integers}$, if $\bar f = R.\mathrm{residue}(f)$ is transcendental over $\kappa$, and if $[F_b : \kappa(\bar f)] = [F : L(f)]$, then all $y_i$ lie in $R.\mathrm{integers}$ and their residues $\bar y_i$ satisfy: the map $q \mapsto \sum_i q_i(\bar f)\,\bar y_i$ from families of polynomials over $\kappa$ to $F_b$ is injective, and every $b \in F_b$ can be written as $\sum_i c_i \bar y_i$ with $c_i \in \kappa(\bar f)$. Thus $\bar y$ is a $\kappa(\bar f)$-basis of $F_b$.
--
--   This is the statement that reduction modulo almost all places of the constant field carries an integral basis of $F$ over $L[f]$ to a basis of the reduced function field over $\kappa(A)(\bar f)$, a step in the reduction theory of one-variable function fields. It is used in the two subsequent results on spanning by, and linear independence of, the residues $\bar y_i$, in particular in the comparison of integrality conditions before and after reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_finset_forall_valuation_eq_one_forall_exists_mem_integers_residue_uniqueRepr_and_span.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem AlgebraicCurve.RegularProlongation.exists_finset_forall_valuation_eq_one_forall_exists_mem_integers_residue_uniqueRepr_and_span
    {L : Type u} [Field L] [IsAlgClosed L]
    {F : Type v} [Field F] [Algebra L F]
    (f : F)
    [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin L ({f} : Set F)) F]
    {ι : Type*} [Fintype ι] (y : ι → F)
    (hcard : Fintype.card ι = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (hyint : ∀ i, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → y i ∈ V)
    (hyli : ∀ c : ι → Polynomial L,
      ∑ i, Polynomial.aeval f (c i) * y i = 0 → ∀ i, c i = 0) :
    ∃ S : Finset L, (∀ s ∈ S, s ≠ 0) ∧
      ∀ A : ValuationSubring L, (∀ s ∈ S, A.valuation s = 1) →
        ∀ (Fb : Type v) [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
          (R : AlgebraicCurve.RegularProlongation A F Fb) (hfR : f ∈ R.integers),
          Transcendental (IsLocalRing.ResidueField A) (R.residue ⟨f, hfR⟩) →
          Module.finrank
              (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb)) Fb
            = Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F →
          ∃ hyO : ∀ i, y i ∈ R.integers,
            (∀ q q' : ι → Polynomial (IsLocalRing.ResidueField A),
              ∑ i, Polynomial.aeval (R.residue ⟨f, hfR⟩) (q i) * R.residue ⟨y i, hyO i⟩
                = ∑ i, Polynomial.aeval (R.residue ⟨f, hfR⟩) (q' i) * R.residue ⟨y i, hyO i⟩ →
              q = q') ∧
            ∀ b : Fb, ∃ c : ι →
                IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue ⟨f, hfR⟩} : Set Fb),
              b = ∑ i, (c i : Fb) * R.residue ⟨y i, hyO i⟩ := by sorry
