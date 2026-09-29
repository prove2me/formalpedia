-- Prove2me | Theorems.Thm_AlgebraicCurve_RegularProlongation_comap_maximalIdeal_eq_span_and_residue_eq_and_ord_eq_one_of_reads_of_constants
-- name    : AlgebraicCurve.RegularProlongation.comap_maximalIdeal_eq_span_and_residue_eq_and_ord_eq_one_of_reads_of_constants
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/0fac891a-2896-5e2b-8d20-d0b43d462733
-- title:
--   Centre, residue character and uniformiser for a read local subring
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, $F$ a field extension of $L$, and $\bar F$ a field extension of the residue field $\kappa(A)$ of $A$. Let $R$ be a regular prolongation of $A$ to $F$ with values in $\bar F$: a valuation subring $\mathcal O_R =$ `R.integers` of $F$ together with a surjective ring homomorphism $\mathrm{res} : \mathcal O_R \to \bar F$ whose kernel is the maximal ideal of $\mathcal O_R$, such that $\mathcal O_R \cap L = A$, such that $\mathrm{res}$ on constants is the map $\kappa(A) \to \bar F$, and such that every nonzero $f \in F$ has an $L$-multiple lying in $\mathcal O_R$ with nonzero reduction. Let $S$ be a Noetherian local subring of $F$ with $S \subseteq \mathcal O_R$. Assume given a family $c : \iota \to A$ of constants whose residues exhaust $\kappa(A)$ and whose images lie in $S$, and a ring homomorphism $\chi : S \to \kappa(A)$ with kernel $\mathfrak m_S$ sending each constant $c_i$ to its residue in $\kappa(A)$. Assume $\varpi, t \in S$ satisfy $\mathfrak m_S = (\varpi, t)$, the image of $\varpi$ lies in the maximal ideal of $\mathcal O_R$, $t \notin (\varpi)$, and $S/(\varpi)$ is a domain; assume some element of $\mathfrak m_S$ has nonzero reduction under $\mathrm{res}$, and that every $g \in \bar F$ is a quotient $\mathrm{res}(a)/\mathrm{res}(b)$ with $a, b \in S$, $\mathrm{res}(b) \neq 0$. Finally let $Q$ be a place of $\bar F$ over $\kappa(A)$, i.e. a valuation subring $\mathcal O_Q \neq \bar F$ of $\bar F$ containing $\kappa(A)$ and a principal ideal ring, and assume $Q$ reads $S$: for every $f \in S$ one has $\mathrm{res}(f) \in \mathcal O_Q$, and $\mathrm{res}(f)$ is a non-unit of $\mathcal O_Q$ exactly when $f \in \mathfrak m_S$. The conclusion has three parts: for $f \in S$, the image of $f$ lies in the maximal ideal of $\mathcal O_R$ if and only if $\varpi \mid f$ in $S$; for $f \in S$, the residue of $\mathrm{res}(f) \in \mathcal O_Q$ in the residue field of $\mathcal O_Q$ is the image of $\chi(f)$ under $\kappa(A) \to \kappa(Q)$; and $\mathrm{ord}_Q(\mathrm{res}(t)) = 1$, where $\mathrm{ord}_Q$ is minus the logarithm of the $\mathbb Z^{m0}$-valued adic valuation attached to $\mathcal O_Q$.
--
--   This is the passage from a local subring $S$ of $F$ read by a place $Q$ of the reduction field to the three pieces of data used downstream: that the centre of the regular prolongation cuts out the principal ideal $(\varpi)$ on $S$, that $\chi$ is the residue character at $Q$ of the reductions of $S$, and that the reduction of the fibre parameter $t$ is a uniformiser at $Q$. It supplies the corresponding clauses of the per-point stalk analysis of the two-chart integral model of the full-level modular curve, in the three declarations [`ModularCurve.FullLevel.exists_stalk_etaleCoordinate_residueChar_of_offBranch_of_reads_twoChartIntegralModel`](thm.html#ModularCurve.FullLevel.exists_stalk_etaleCoordinate_residueChar_of_offBranch_of_reads_twoChartIntegralModel), `…_of_eq_three` and `…_of_eq_two`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_RegularProlongation_comap_maximalIdeal_eq_span_and_residue_eq_and_ord_eq_one_of_reads_of_constants.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing AlgebraicCurve

theorem AlgebraicCurve.RegularProlongation.comap_maximalIdeal_eq_span_and_residue_eq_and_ord_eq_one_of_reads_of_constants
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar)
    (S : Subring F) [IsLocalRing ↥S] [IsNoetherianRing ↥S]
    (hSR : ∀ f : ↥S, (f : F) ∈ R.integers)

    {ι : Type*} (cst : ι → ↥A)
    (hκ : Function.Surjective (fun i => IsLocalRing.residue ↥A (cst i)))
    (hAS : ∀ i : ι, algebraMap L F (cst i : L) ∈ S)
    (χ : ↥S →+* ResidueField A)
    (hker : RingHom.ker χ = maximalIdeal ↥S)
    (hχA : ∀ i : ι, χ ⟨algebraMap L F (cst i : L), hAS i⟩ = IsLocalRing.residue ↥A (cst i))

    (ϖS t : ↥S)
    (hmax : maximalIdeal ↥S = Ideal.span {ϖS, t})
    (hϖR : (⟨(ϖS : F), hSR ϖS⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers)
    (ht : t ∉ Ideal.span {ϖS})
    (hdom : IsDomain (↥S ⧸ Ideal.span {ϖS}))

    (hng : ∃ f : ↥S, f ∈ maximalIdeal ↥S ∧ R.residue ⟨(f : F), hSR f⟩ ≠ 0)

    (hfracbar : ∀ g : Fbar, ∃ a b : ↥S, R.residue ⟨(b : F), hSR b⟩ ≠ 0 ∧
      g * R.residue ⟨(b : F), hSR b⟩ = R.residue ⟨(a : F), hSR a⟩)

    (Q : Place (ResidueField A) Fbar)
    (hreads : ∀ f : ↥S, R.residue ⟨(f : F), hSR f⟩ ∈ Q.toValuationSubring ∧
      (R.residue ⟨(f : F), hSR f⟩ ∈ Q.toValuationSubring.nonunits ↔ f ∈ maximalIdeal ↥S)) :

    (∀ f : ↥S, (⟨(f : F), hSR f⟩ : ↥R.integers) ∈ maximalIdeal ↥R.integers ↔ ϖS ∣ f) ∧

    (∀ f : ↥S, ∃ hm : R.residue ⟨(f : F), hSR f⟩ ∈ Q.toValuationSubring,
      IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hSR f⟩, hm⟩ =
        algebraMap (ResidueField ↥A) Q.ResidueField (χ f)) ∧

    Q.ord (R.residue ⟨(t : F), hSR t⟩) = 1 := by sorry
