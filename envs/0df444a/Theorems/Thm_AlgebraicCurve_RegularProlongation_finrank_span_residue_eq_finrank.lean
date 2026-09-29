-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank
-- name    : AlgebraicCurve.RegularProlongation.finrank_span_residue_eq_finrank
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/3d47930d-689b-5bdf-9960-ae796fc03d50
-- title:
--   Reduction preserves dimension of finite-dimensional linear systems
-- statement:
--   Let $L$ be a field and $A \subseteq L$ a valuation subring, with residue field $k = \mathrm{ResidueField}(A)$; let $F$ be a field extension of $L$ and $\bar F$ a field extension of $k$. Let $R$ be a regular prolongation of $A$ to $F$ with values in $\bar F$, that is: a valuation subring $\mathcal O = R.\mathrm{integers}$ of $F$, a ring homomorphism $\mathrm{res} \colon \mathcal O \to \bar F$, such that for $x \in L$ one has $\mathrm{algebraMap}(x) \in \mathcal O$ exactly when $x \in A$, $\mathrm{res}$ is surjective with kernel the maximal ideal of $\mathcal O$, $\mathrm{res}$ agrees on elements of $A$ with the residue map $A \to k$ followed by $k \to \bar F$, and every nonzero $f \in F$ admits $c \in L$ with $c \cdot f \in \mathcal O$ and $\mathrm{res}(c \cdot f) \neq 0$. Let $x \in \mathcal O$ be such that $\mathrm{res}(x)$ is transcendental over $k$, such that $\bar F$ has positive (hence finite) $k(\mathrm{res}(x))$-rank, and such that $[F : L(x)] = [\bar F : k(\mathrm{res}(x))]$, the two degrees being taken as $\mathrm{Module.finrank}$ over the respective simple intermediate fields. Then for every finite-dimensional $L$-subspace $V \subseteq F$, the $k$-span inside $\bar F$ of the set of residues $\mathrm{res}(f)$ of elements $f \in \mathcal O$ with $f \in V$ has $k$-dimension equal to $\dim_L V$.
--
--   This is the dimension-preservation statement for reduction of a function field modulo a regular prolongation, in the form used by Deuring and by Shimura–Taniyama: passing to residues neither collapses nor enlarges a finite-dimensional linear system. It is used in the comparison of Riemann–Roch spaces under place reduction and in the surjectivity of reduction on integral closures, and hence in the control of the genus under reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_finrank_span_residue_eq_finrank.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.finrank_span_residue_eq_finrank
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (x : R.integers) (hx : Transcendental (IsLocalRing.ResidueField A) (R.residue x))
    (hfin : 0 < Module.finrank
      (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (hdeg : Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({R.residue x} : Set Fbar)) Fbar)
    (V : Submodule L F) [FiniteDimensional L V] :
    Module.finrank (IsLocalRing.ResidueField A)
        (Submodule.span (IsLocalRing.ResidueField A)
          {h : Fbar | ∃ f : R.integers, (f : F) ∈ V ∧ R.residue f = h}) =
      Module.finrank L V := by sorry
