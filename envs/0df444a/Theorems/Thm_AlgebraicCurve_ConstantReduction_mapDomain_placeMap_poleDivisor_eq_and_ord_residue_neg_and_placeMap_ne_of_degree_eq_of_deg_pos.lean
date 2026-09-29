-- Prove2me | Theorems.Thm_AlgebraicCurve_ConstantReduction_mapDomain_placeMap_poleDivisor_eq_and_ord_residue_neg_and_placeMap_ne_of_degree_eq_of_deg_pos
-- name    : AlgebraicCurve.ConstantReduction.mapDomain_placeMap_poleDivisor_eq_and_ord_residue_neg_and_placeMap_ne_of_degree_eq_of_deg_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/2c6ce59f-35f1-52a0-b170-d94507c440d9
-- title:
--   Poles reduce to poles under a degree-preserving constant reduction
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, $F$ a field extension of $L$ in which every nonzero function has a finitely supported principal divisor of degree $0$ (`HasPrincipalDivisors`), and $\bar F$ a field extension of the residue field $k = A/\mathfrak m_A$. Let $R$ be a constant reduction of $F$ along $A$ onto $\bar F$, that is: a valuation subring $\mathcal O = R.\mathrm{integers}$ of $F$, a surjective ring homomorphism $R.\mathrm{residue} \colon \mathcal O \to \bar F$ with kernel the maximal ideal of $\mathcal O$, and a map $r = R.\mathrm{placeMap}$ from places of $F/L$ to places of $\bar F/k$, subject to: $\mathrm{algebraMap}\,x \in \mathcal O \iff x \in A$ for $x \in L$, compatibility of $R.\mathrm{residue}$ with the residue map of $A$ on constants, the existence for each $f \neq 0$ of $c \in L$ with $c \cdot f \in \mathcal O$ of nonzero residue, $\deg r(P) = \deg P$ for all $P$ (degrees being residue-field degrees over the constant field), and $r_*(\mathrm{div}\,f) = \mathrm{div}(\overline f)$ for $f \in \mathcal O$ with $\overline f \neq 0$. Let $u \in \mathcal O$, let $D_u$ be the divisor with $D_u(P) = \max(0, -\mathrm{ord}_P u)$ for every place $P$ of $F/L$, and $D_{\bar u}$ the divisor with $D_{\bar u}(Q) = \max(0, -\mathrm{ord}_Q \overline u)$ for every place $Q$ of $\bar F/k$, where $\overline u = R.\mathrm{residue}(u)$. Assume $\deg D_{\bar u} = \deg D_u$, $D_{\bar u} \neq 0$, and $\deg P > 0$ for every place $P$ with $\mathrm{ord}_P u < 0$. Then: (a) the push-forward $r_* D_u$ equals $D_{\bar u}$; (b) for every place $P'$ with $\mathrm{ord}_{P'} u < 0$ one has $\mathrm{ord}_{r(P')} \overline u < 0$; and (c) for every place $P$ that is rational (the structure map $L \to$ residue field of $P$ being surjective) with $u$ in the valuation subring of $P$ and $P$-value $\mathrm{evalAt}_P(u) \in A$, one has $r(P') \neq r(P)$ for every place $P'$ with $\mathrm{ord}_{P'} u < 0$.
--
--   This is the basic comparison of pole divisors in Deuring's theory of constant reduction of algebraic function fields: under equality of pole-divisor degrees, the reduction of places carries the pole divisor of $u$ onto that of its residue, poles go to poles, and no pole collides with a rational place where $u$ takes an $A$-integral value. It is used in the analysis of modular curves over a valuation ring, where $u$ plays the role of a modular function with poles at the cusps and the conclusion separates reductions of cusps from reductions of points with integral $j$-invariant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ConstantReduction_mapDomain_placeMap_poleDivisor_eq_and_ord_residue_neg_and_placeMap_ne_of_degree_eq_of_deg_pos.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.ConstantReduction.mapDomain_placeMap_poleDivisor_eq_and_ord_residue_neg_and_placeMap_ne_of_degree_eq_of_deg_pos
    {L : Type} [Field L] {A : ValuationSubring L}
    {F : Type} [Field F] [Algebra L F] [HasPrincipalDivisors L F]
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : ConstantReduction A F Fbar)
    (u : F) (hu : u ∈ R.integers)
    (Du : Divisor L F) (hDu : ∀ P : Place L F, Du P = max 0 (-(P.ord u)))
    (Dū : Divisor (ResidueField ↥A) Fbar)
    (hDū : ∀ Q : Place (ResidueField ↥A) Fbar, Dū Q = max 0 (-(Q.ord (R.residue ⟨u, hu⟩))))
    (hdeg : Divisor.degree Dū = Divisor.degree Du) (hnc : Dū ≠ 0)
    (hfin : ∀ P : Place L F, P.ord u < 0 → 0 < P.deg) :
    Finsupp.mapDomain R.placeMap Du = Dū ∧
    (∀ P' : Place L F, P'.ord u < 0 → (R.placeMap P').ord (R.residue ⟨u, hu⟩) < 0) ∧
    (∀ P : Place L F, P.IsRational → u ∈ P.toValuationSubring → P.evalAt u ∈ A →
      ∀ P' : Place L F, P'.ord u < 0 → R.placeMap P' ≠ R.placeMap P) := by sorry
