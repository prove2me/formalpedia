-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_mapDomain_and_slope_of_valuation_lt_of_exists_lt
-- name    : AlgebraicCurve.Annulus.mapDomain_and_slope_of_valuation_lt_of_exists_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/42028134-199f-59f9-899a-fb801d7a3721
-- title:
--   Slopes across an interior circle of an annulus
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, $F/L$ a field extension and $An$ an annulus over $A$ in $F$, with domain $An.\mathrm{dom}$ a set of places of $F/L$ (valuation subrings of $F$ containing $L$, proper and principal), parameter $z = An.\mathrm{param}$ and modulus in the maximal ideal of $A$; here $P.\mathrm{ord}$ is minus the logarithm of the adic valuation attached to $P$, and $P.\mathrm{evalAt}\,f \in L$ is the value of $f$ at $P$ (the preimage in $L$ of the residue of $f$, for $f$ in the valuation subring of $P$, and $0$ otherwise). Assume: every nonzero $f \in F$ has only finitely many places of $An.\mathrm{dom}$ with $P.\mathrm{ord}\,f \ne 0$; $c \in L$ satisfies $v(An.\mathrm{modulus}) < v(c) < 1$ for the valuation $v$ of $A$; the residue field $k$ of $A$ is infinite; there exist $b$ with $v(c) < v(b) < 1$ and $b'$ with $v(An.\mathrm{modulus}) < v(b') < v(c)$. Let $V$ be a valuation subring of $F$ consisting exactly of those $f$ for which some finite set $t \subseteq k$ has the property that every $P \in An.\mathrm{dom}$ with $c^{-1}z(P) \in A$, $v(z(P)) = v(c)$ and residue of $c^{-1}z(P)$ outside $t$ satisfies $f \in P$ and $P.\mathrm{evalAt}\,f \in A$; assume $V \cap L = A$. Let $\mathrm{res} \colon V \to k(X)$ be a surjective ring homomorphism with kernel the maximal ideal of $V$, sending each $a \in A$ to its residue in $k$ and $c^{-1}z$ to $X$. Assume further (hpt) that for $P \in An.\mathrm{dom}$ rational with $v(z(P)) = v(c)$, and $f \in V$ lying in every $w \in An.\mathrm{dom}$ on that circle having the same residue of $c^{-1}z(w)$ as $P$, one has $\mathrm{res}\,f$ in the valuation subring of the place $\mathrm{placeOfPoint}$ at the residue $\bar{\alpha}$ of $c^{-1}z(P)$, $P.\mathrm{evalAt}\,f \in A$, and the residue of $P.\mathrm{evalAt}\,f$ maps to the residue of $\mathrm{res}\,f$ at that place; and let $pm$ be a map from places of $F/L$ to places of $k(X)/k$ which on the circle sends $P$ to $\mathrm{placeOfPoint}(\bar{\alpha})$. The conclusion has three parts. (1) For $f \in V$ with $\mathrm{res}\,f \ne 0$ and any divisor $D$ on places of $F/L$ with $D(P) = P.\mathrm{ord}\,f$ for $P \in An.\mathrm{dom}$ on the circle $v(z(P)) = v(c)$ and $D(P) = 0$ elsewhere, the pushforward $\mathrm{Finsupp.mapDomain}\ pm\ D$ takes at every place $Q$ of $k(X)/k$ with $Q \ne \mathrm{placeOfPoint}\,0$ and $X \in Q$ the value $Q.\mathrm{ord}(\mathrm{res}\,f)$. (2) For $b \in L$ with $v(An.\mathrm{modulus}) \le v(b) < v(c)$ and $f \in V$ with $\mathrm{res}\,f \ne 0$ having $P.\mathrm{ord}\,f = 0$ for all $P \in An.\mathrm{dom}$ with $v(b) < v(z(P)) < v(c)$: for each such $P$, the element $P.\mathrm{evalAt}\,f \cdot (c^{-1}z(P))^{-m}$, with $m$ the order of $\mathrm{res}\,f$ at $\mathrm{placeOfPoint}\,0$, lies in $A$ and is a unit there. (3) Symmetrically, for $a \in L$ with $v(c) < v(a) \le 1$ and $f \in V$ with $\mathrm{res}\,f \ne 0$ having no zeros or poles on $v(c) < v(z(P)) < v(a)$: for every place $x$ of $k(X)/k$ with $X \notin x$ and every such $P$, the element $P.\mathrm{evalAt}\,f \cdot (c\, z(P)^{-1})^{-x.\mathrm{ord}(\mathrm{res}\,f)}$ lies in $A$ and is a unit there.
--
--   This is the divisor compatibility of the reduction map on an interior circle $v(z) = v(c)$ of an annulus together with the statement that $|f|$ is exactly monomial, with slopes given by the orders of $\mathrm{res}\,f$ at $0$ and at $\infty$, on the two adjacent bands. It is used in the construction of the component chart attached to such a circle, [`AlgebraicCurve.Annulus.exists_componentChart_ratFunc_of_valuation_lt_of_exists_lt`](thm.html#AlgebraicCurve.Annulus.exists_componentChart_ratFunc_of_valuation_lt_of_exists_lt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_mapDomain_and_slope_of_valuation_lt_of_exists_lt.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_StandardAnnulus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing AlgebraicCurve.RationalFunctionField

theorem AlgebraicCurve.Annulus.mapDomain_and_slope_of_valuation_lt_of_exists_lt
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    (An : Annulus A F)
    (hfin : ∀ f : F, f ≠ 0 → {P : Place L F | P ∈ An.dom ∧ P.ord f ≠ 0}.Finite)
    (c : L) (hc : A.valuation ((An.modulus : A) : L) < A.valuation c ∧ A.valuation c < 1)
    (hinf : Infinite (IsLocalRing.ResidueField A))
    (hR : (∃ b : L, A.valuation c < A.valuation b ∧ A.valuation b < 1) ∧
      (∃ b : L, A.valuation ((An.modulus : A) : L) < A.valuation b ∧ A.valuation b < A.valuation c))
    (V : ValuationSubring F)
    (hV : ∀ f : F, f ∈ V ↔ ∃ t : Finset (IsLocalRing.ResidueField A), ∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A,
      A.valuation (P.evalAt An.param) = A.valuation c → IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩ ∉ t → f ∈ P.toValuationSubring ∧ P.evalAt f ∈ A)
    (hVA : ∀ x : L, algebraMap L F x ∈ V ↔ x ∈ A)
    (res : ↥V →+* RatFunc (IsLocalRing.ResidueField A))
    (hsurj : Function.Surjective res) (hker : RingHom.ker res = IsLocalRing.maximalIdeal ↥V)
    (hconst : ∀ (a : A) (ha : algebraMap L F (a : L) ∈ V),
      res ⟨algebraMap L F (a : L), ha⟩ = algebraMap (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)) (IsLocalRing.residue A a))
    (hX : ∀ hz : algebraMap L F c⁻¹ * An.param ∈ V, res ⟨algebraMap L F c⁻¹ * An.param, hz⟩ = (RatFunc.X : RatFunc (IsLocalRing.ResidueField A)))
    (hpt : ∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A, A.valuation (P.evalAt An.param) = A.valuation c → P.IsRational →
          ∀ (f : F) (hf : f ∈ V),
            (∀ w ∈ An.dom, ∀ h' : c⁻¹ * w.evalAt An.param ∈ A, A.valuation (w.evalAt An.param) = A.valuation c →
                IsLocalRing.residue A ⟨c⁻¹ * w.evalAt An.param, h'⟩ = IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩ → f ∈ w.toValuationSubring) →
            ∃ (hm : (res ⟨f, hf⟩ : RatFunc (IsLocalRing.ResidueField A)) ∈ (placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)).toValuationSubring)
              (hv : P.evalAt f ∈ A),
              algebraMap (IsLocalRing.ResidueField A) (placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)).ResidueField
                  (IsLocalRing.residue A ⟨P.evalAt f, hv⟩) =
                IsLocalRing.residue (placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)).toValuationSubring ⟨res ⟨f, hf⟩, hm⟩)
    (pm : Place L F → Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)))
    (hpm : ∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A, A.valuation (P.evalAt An.param) = A.valuation c →
      pm P = placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)) :
    (∀ (f : ↥V), res f ≠ 0 → ∀ D : Divisor L F,
        (∀ P, P ∈ An.dom ∧ A.valuation (P.evalAt An.param) = A.valuation c → D P = P.ord (f : F)) →
        (∀ P, ¬ (P ∈ An.dom ∧ A.valuation (P.evalAt An.param) = A.valuation c) → D P = 0) →
          ∀ Q : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)), Q ≠ placeOfPoint (IsLocalRing.ResidueField A) 0 →
            (RatFunc.X : RatFunc (IsLocalRing.ResidueField A)) ∈ Q.toValuationSubring →
            Finsupp.mapDomain pm D Q = Q.ord (res f)) ∧
    (∀ (b : L), A.valuation ((An.modulus : A) : L) ≤ A.valuation b → A.valuation b < A.valuation c →
      ∀ (f : F) (hf : f ∈ V), res ⟨f, hf⟩ ≠ 0 →
        (∀ P ∈ An.dom, A.valuation b < A.valuation (P.evalAt An.param) →
          A.valuation (P.evalAt An.param) < A.valuation c → P.ord f = 0) →
        ∀ P ∈ An.dom, A.valuation b < A.valuation (P.evalAt An.param) →
          A.valuation (P.evalAt An.param) < A.valuation c →
          ∃ h : P.evalAt f * (c⁻¹ * P.evalAt An.param) ^
              (-((placeOfPoint (IsLocalRing.ResidueField A) 0).ord (res ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A)) ∧
    (∀ (a : L), A.valuation c < A.valuation a → A.valuation a ≤ 1 →
      ∀ (f : F) (hf : f ∈ V), res ⟨f, hf⟩ ≠ 0 →
        (∀ P ∈ An.dom, A.valuation c < A.valuation (P.evalAt An.param) →
          A.valuation (P.evalAt An.param) < A.valuation a → P.ord f = 0) →
        ∀ x : Place (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)), (RatFunc.X : RatFunc (IsLocalRing.ResidueField A)) ∉ x.toValuationSubring →
        ∀ P ∈ An.dom, A.valuation c < A.valuation (P.evalAt An.param) →
          A.valuation (P.evalAt An.param) < A.valuation a →
          ∃ h : P.evalAt f * (c * (P.evalAt An.param)⁻¹) ^
              (-(x.ord (res ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : A)) := by sorry
