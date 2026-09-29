-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_exists_componentChart_ratFunc_of_valuation_lt_of_exists_lt
-- name    : AlgebraicCurve.Annulus.exists_componentChart_ratFunc_of_valuation_lt_of_exists_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/517e305e-3de8-5555-8ad4-1a49ec1af77f
-- title:
--   Circle charts inside an annulus over a valuation ring
-- statement:
--   Let $L$ be an algebraically closed field, $A\subseteq L$ a valuation subring with residue field $\kappa$, and $F$ a field extension of $L$ satisfying `IsCurveOver L F` (principal divisors of degree zero exist, every place has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one). Let `An` be an `Annulus A F`: a set `An.dom` of places of $F/L$, a parameter $z=$ `An.param` and a modulus $\mu\in\mathfrak m_A$ such that each $P\in$ `An.dom` is rational with $z(P)=P.\mathrm{evalAt}\,z\in\mathfrak m_A\setminus\{0\}$ and $\mu=z(P)m$ for some $m\in\mathfrak m_A$, each admissible value in $\mathfrak m_A$ is attained by exactly one $P\in$ `An.dom`, $\operatorname{ord}_P(z-z(P))=1$, and the unit principle holds. Let $c\in L$ with $v(\mu)<v(c)<1$ (for $v=$ `A.valuation`), assume both adjacent bands contain the valuation of a constant, i.e. some $b$ with $v(c)<v(b)<1$ and some $b$ with $v(\mu)<v(b)<v(c)$, and let $Q_\infty$ be a place of $\kappa(X)/\kappa$ with $X$ not in its valuation subring. Then there is a `ComponentChart A F (RatFunc κ)` $\mathcal C$ — a valuation subring `integers` of $F$ with a surjective residue map onto $\kappa(X)$ whose kernel is the maximal ideal, inducing $A$ on constants, together with a domain of places, a finite set of nodes and a map `placeMap` satisfying the chart axioms — such that: its domain is $\{P\in\mathrm{dom}\,\mathcal A: v(z(P))=v(c)\}$; its nodes are the point $X=0$ of $\kappa(X)$ and $Q_\infty$; $c^{-1}z$ lies in `integers` and reduces to $X$; `placeMap` sends $P$ to the point of $\kappa(X)$ given by the residue of $c^{-1}z(P)$; over every non-node place $Q$ of $\kappa(X)$ there is $T\in$ `integers` whose reduction is nonzero with $\operatorname{ord}_Q=1$, which lies in the valuation ring of every $P$ in the fibre of `placeMap` over $Q$ with $T(P)\in\mathfrak m_A$, and which takes each value of $\mathfrak m_A$ at exactly one such $P$; every place in the chart's domain is rational; and two slope laws hold: for $b$ with $v(\mu)\le v(b)<v(c)$ and $f\in$ `integers` with nonzero reduction and no zero or pole on the inner band $v(b)<v(z(P))<v(c)$, the element $f(P)\,(c^{-1}z(P))^{-\operatorname{ord}_{X=0}\bar f}$ lies in $A$ and is a unit for all $P$ on that band, and symmetrically, for $a$ with $v(c)<v(a)\le 1$ and $f$ with nonzero reduction and no zero or pole on the outer band $v(c)<v(z(P))<v(a)$, the element $f(P)\,(c\,z(P)^{-1})^{-\operatorname{ord}_{Q_\infty}\bar f}$ lies in $A$ and is a unit there.
--
--   This packages the Gauss point of the circle $|z|=|c|$ inside an annulus as a single component chart onto the rational function field over the residue field, recording its domain, its two nodes, the identification of $c^{-1}z$ with the coordinate $X$, the disc shape of the fibres of the reduction map, and the behaviour of orders of vanishing on the two adjacent bands. It is used in the construction of semistable coverings, via [`AlgebraicCurve.SemistableCovering.exists_circleCharts_and_bands_width_one_of_discFibres_of_rankOne`](thm.html#AlgebraicCurve.SemistableCovering.exists_circleCharts_and_bands_width_one_of_discFibres_of_rankOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_exists_componentChart_ratFunc_of_valuation_lt_of_exists_lt.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.RationalFunctionField
open Classical in

theorem AlgebraicCurve.Annulus.exists_componentChart_ratFunc_of_valuation_lt_of_exists_lt
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (F : Type*) [Field F] [Algebra L F] [IsCurveOver L F]
    (An : Annulus A F)
    (c : L) (hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1)
    (hR : (∃ b : L, A.valuation c < A.valuation b ∧ A.valuation b < 1) ∧
      (∃ b : L, A.valuation ((An.modulus : A) : L) < A.valuation b ∧ A.valuation b < A.valuation c))
    (Qinf : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)))
    (hQinf : (RatFunc.X : RatFunc (IsLocalRing.ResidueField A)) ∉ Qinf.toValuationSubring) :
    ∃ Cc : ComponentChart A F (RatFunc (IsLocalRing.ResidueField A)),

      Cc.dom = {P | P ∈ An.dom ∧ A.valuation (P.evalAt An.param) = A.valuation c} ∧
      Cc.nodes = {placeOfPoint (IsLocalRing.ResidueField A) 0, Qinf} ∧
      (∃ h : (algebraMap L F c)⁻¹ * An.param ∈ Cc.integers,
          Cc.residue ⟨_, h⟩ = (RatFunc.X : RatFunc (IsLocalRing.ResidueField A))) ∧
      (∀ P ∈ Cc.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A,
          Cc.placeMap P = placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨_, h⟩)) ∧

      (∀ Q : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)), Q ∉ Cc.nodes →
        ∃ (T : F) (hT : T ∈ Cc.integers), Cc.residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord (Cc.residue ⟨T, hT⟩) = 1 ∧
          (∀ P ∈ Cc.dom, Cc.placeMap P = Q → T ∈ P.toValuationSubring ∧
            ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
          ∀ c' : A, c' ∈ IsLocalRing.maximalIdeal A →
            ∃! P : Place L F, P ∈ Cc.dom ∧ Cc.placeMap P = Q ∧ P.evalAt T = c') ∧

      (∀ P ∈ Cc.dom, P.IsRational) ∧

      (∀ b : L, A.valuation ((An.modulus : A) : L) ≤ A.valuation b → A.valuation b < A.valuation c →
        ∀ (f : F) (hf : f ∈ Cc.integers), Cc.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, A.valuation b < A.valuation (P.evalAt An.param) →
            A.valuation (P.evalAt An.param) < A.valuation c → P.ord f = 0) →
          ∀ P ∈ An.dom, A.valuation b < A.valuation (P.evalAt An.param) →
            A.valuation (P.evalAt An.param) < A.valuation c →
            ∃ h : P.evalAt f * (c⁻¹ * P.evalAt An.param) ^
                (-((placeOfPoint (IsLocalRing.ResidueField A) 0).ord (Cc.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A)) ∧

      (∀ a : L, A.valuation c < A.valuation a → A.valuation a ≤ 1 →
        ∀ (f : F) (hf : f ∈ Cc.integers), Cc.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, A.valuation c < A.valuation (P.evalAt An.param) →
            A.valuation (P.evalAt An.param) < A.valuation a → P.ord f = 0) →
          ∀ P ∈ An.dom, A.valuation c < A.valuation (P.evalAt An.param) →
            A.valuation (P.evalAt An.param) < A.valuation a →
            ∃ h : P.evalAt f * (c * (P.evalAt An.param)⁻¹) ^
                (-(Qinf.ord (Cc.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A)) := by sorry
