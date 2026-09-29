-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_exists_norm_mem_integers_and_residue_norm_eq_norm_residue
-- name    : AlgebraicCurve.RegularProlongation.exists_norm_mem_integers_and_residue_norm_eq_norm_residue
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/b70af626-f0ae-52e5-85df-711f5927233d
-- title:
--   Norms commute with reduction for compatible regular prolongations
-- statement:
--   Let $L$ be a field with a valuation subring $A \subseteq L$, let $F$ and $F'$ be extension fields of $L$, and let $k$, $k'$ be fields equipped with algebra structures over the residue field of $A$. Let $R$ be a regular prolongation of $A$ to $F$ with values in $k$ and $R'$ one of $A$ to $F'$ with values in $k'$: that is, each consists of a valuation subring $\mathrm{integers}$ of the field together with a surjective ring homomorphism $\mathrm{residue}$ to the residue field whose kernel is the maximal ideal, such that an element of $L$ lands in $\mathrm{integers}$ exactly when it lies in $A$, the residue map is compatible with $A \to \mathrm{ResidueField}\,A$ on elements of $A$, and every nonzero element of the field admits a scaling by some $c \in L$ which is integral with nonzero residue. Let $\varphi : F \to F'$ be an $L$-algebra map and $\iota : k \to k'$ a ring homomorphism, compatible in the sense that $\varphi f \in R'.\mathrm{integers}$ if and only if $f \in R.\mathrm{integers}$, and that $R'.\mathrm{residue}(\varphi f) = \iota\bigl(R.\mathrm{residue}(f)\bigr)$ for $f$ integral. Let $n$ be a natural number equal to the dimension of $F'$ as an $F$-vector space via $\varphi$, and let $b_1,\dots,b_n$ be elements of $R'.\mathrm{integers}$ whose residues are linearly independent over $k$ (acting through $\iota$) and span $k'$ over $k$. Then for every $h \in R'.\mathrm{integers}$ the norm $N_{F'/F}(h)$, formed for the $F$-algebra structure on $F'$ given by $\varphi$, lies in $R.\mathrm{integers}$, and its residue under $R.\mathrm{residue}$ equals the norm over $k$ (for the $k$-algebra structure on $k'$ given by $\iota$) of the residue $R'.\mathrm{residue}(h)$.
--
--   This is the statement that, for a residually full (degree-preserving) compatible pair of regular prolongations, taking the field norm commutes with reduction: integral elements have integral norms, and the reduction of the norm is the norm of the reduction. It is used in the computation of reduced root functions on modular curves, where a norm along a finite map of curves has to be compared with the corresponding norm on residue fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_exists_norm_mem_integers_and_residue_norm_eq_norm_residue.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.exists_norm_mem_integers_and_residue_norm_eq_norm_residue
    {L F F' k k' : Type*} [Field L] [Field F] [Field F'] [Field k] [Field k']
    [Algebra L F] [Algebra L F']
    (A : ValuationSubring L) [Algebra (IsLocalRing.ResidueField ↥A) k] [Algebra (IsLocalRing.ResidueField ↥A) k']
    (R : AlgebraicCurve.RegularProlongation A F k) (R' : AlgebraicCurve.RegularProlongation A F' k')
    (φ : F →ₐ[L] F') (ι : k →+* k')

    (hint : ∀ f : F, φ f ∈ R'.integers ↔ f ∈ R.integers)
    (hres : ∀ (f : F) (hf : f ∈ R.integers) (hf' : φ f ∈ R'.integers), R'.residue ⟨φ f, hf'⟩ = ι (R.residue ⟨f, hf⟩))

    (n : ℕ) (hn : AlgebraicCurve.finrankAlong L φ = n)
    (b : Fin n → F') (hb : ∀ i, b i ∈ R'.integers)
    (hli : letI := ι.toAlgebra; LinearIndependent k (fun i => R'.residue ⟨b i, hb i⟩))
    (hsp : letI := ι.toAlgebra; Submodule.span k (Set.range (fun i => R'.residue ⟨b i, hb i⟩)) = ⊤)
    (h : F') (hh : h ∈ R'.integers) :
    ∃ hN : (letI := AlgebraicCurve.algebraAlong φ; Algebra.norm F h) ∈ R.integers,
      R.residue ⟨_, hN⟩ = (letI := ι.toAlgebra; Algebra.norm k (R'.residue ⟨h, hh⟩)) := by sorry
