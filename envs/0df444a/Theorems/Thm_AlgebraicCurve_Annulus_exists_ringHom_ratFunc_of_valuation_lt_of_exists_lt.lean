-- Prove2me | Theorems.Thm_AlgebraicCurve_Annulus_exists_ringHom_ratFunc_of_valuation_lt_of_exists_lt
-- name    : AlgebraicCurve.Annulus.exists_ringHom_ratFunc_of_valuation_lt_of_exists_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/14664a24-1c77-5de7-bf91-86131196d1e9
-- title:
--   Reduction of the Gauss ring of an interior circle onto k(X)
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring with residue field $k$, and $F$ a field extension of $L$; let $\mathrm{An}$ be an annulus datum for $A$ in $F$, consisting of a set $\mathrm{An.dom}$ of places of $F$ over $L$ (valuation subrings of $F$ containing $L$, proper, with principal ideals), a parameter $z = \mathrm{An.param} \in F$ and a modulus in the maximal ideal of $A$, subject to the axioms of `Annulus` (each $P \in \mathrm{An.dom}$ is rational with $z$ a unit-free parameter whose value $P(z) = P.\mathrm{evalAt}\,z$ lies in the maximal ideal of $A$ and divides the modulus, the values $P(z)$ parametrise $\mathrm{An.dom}$ bijectively, $P.\mathrm{ord}(z - P(z)) = 1$, and the unit principle for functions of order $0$ everywhere on $\mathrm{An.dom}$). Assume: every nonzero $f \in F$ has $P.\mathrm{ord}\,f \neq 0$ for only finitely many $P \in \mathrm{An.dom}$; $c \in L$ satisfies $v(\mathrm{An.modulus}) < v(c) < 1$ for the valuation $v$ of $A$; $k$ is infinite; there exist $b, b' \in L$ with $v(c) < v(b) < 1$ and $v(\mathrm{An.modulus}) < v(b') < v(c)$; and $V$ is a valuation subring of $F$ whose members are exactly those $f \in F$ for which some finite set $t \subseteq k$ has the property that every $P \in \mathrm{An.dom}$ with $c^{-1}P(z) \in A$, $v(P(z)) = v(c)$ and $\overline{c^{-1}P(z)} \notin t$ satisfies $f \in P$ and $P.\mathrm{evalAt}\,f \in A$; finally $V \cap L = A$, in the sense that $x \in L$ has $x \in V$ iff $x \in A$. Then there is a ring homomorphism $\mathrm{res} \colon V \to k(X)$ which is surjective, has kernel the maximal ideal of $V$, sends each $a \in A$ (viewed in $V$) to the constant $\bar a \in k \subseteq k(X)$ and sends $c^{-1}z$ to $X$; moreover every nonzero $f \in F$ admits $a \in L$ with $a \cdot f \in V$ and $\mathrm{res}(a f) \neq 0$; and $\mathrm{res}$ is pointwise compatible with evaluation: if $P \in \mathrm{An.dom}$ is rational with $c^{-1}P(z) \in A$ and $v(P(z)) = v(c)$, and $f \in V$ lies in the valuation subring of every $w \in \mathrm{An.dom}$ with $c^{-1}w(z) \in A$, $v(w(z)) = v(c)$ and $\overline{c^{-1}w(z)} = \overline{c^{-1}P(z)}$, then $\mathrm{res}\,f$ lies in the valuation subring of the place `placeOfPoint` of $k(X)$ attached to the point $\overline{c^{-1}P(z)} \in k$, one has $P.\mathrm{evalAt}\,f \in A$, and the residue of $\mathrm{res}\,f$ at that place is the image of $\overline{P.\mathrm{evalAt}\,f} \in k$ in the residue field of that place.
--
--   This is the construction of the reduction homomorphism of the Gauss ring of the interior circle $v(z) = v(c)$ of an annulus onto the rational function field $k(X)$ over the residue field of $A$, together with the identification of the reduction of a function regular on a residue class with its value there. It is used to produce the chart of the corresponding component of the semistable reduction, in [`AlgebraicCurve.Annulus.exists_componentChart_ratFunc_of_valuation_lt_of_exists_lt`](thm.html#AlgebraicCurve.Annulus.exists_componentChart_ratFunc_of_valuation_lt_of_exists_lt), and rests on the factorisation of a function along the annulus and the unit principle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Annulus_exists_ringHom_ratFunc_of_valuation_lt_of_exists_lt.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_StandardAnnulus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing AlgebraicCurve.RationalFunctionField

theorem AlgebraicCurve.Annulus.exists_ringHom_ratFunc_of_valuation_lt_of_exists_lt
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
    (hVA : ∀ x : L, algebraMap L F x ∈ V ↔ x ∈ A) :
    ∃ res : ↥V →+* RatFunc (IsLocalRing.ResidueField A),
      Function.Surjective res ∧
      RingHom.ker res = IsLocalRing.maximalIdeal ↥V ∧
      (∀ (a : A) (ha : algebraMap L F (a : L) ∈ V),
          res ⟨algebraMap L F (a : L), ha⟩ = algebraMap (IsLocalRing.ResidueField A) (RatFunc (IsLocalRing.ResidueField A)) (IsLocalRing.residue A a)) ∧
      (∀ hz : algebraMap L F c⁻¹ * An.param ∈ V, res ⟨algebraMap L F c⁻¹ * An.param, hz⟩ = (RatFunc.X : RatFunc (IsLocalRing.ResidueField A))) ∧
      (∀ f : F, f ≠ 0 → ∃ a : L, ∃ h : a • f ∈ V, res ⟨a • f, h⟩ ≠ 0) ∧
      (∀ P ∈ An.dom, ∀ h : c⁻¹ * P.evalAt An.param ∈ A, A.valuation (P.evalAt An.param) = A.valuation c → P.IsRational →
          ∀ (f : F) (hf : f ∈ V),
            (∀ w ∈ An.dom, ∀ h' : c⁻¹ * w.evalAt An.param ∈ A, A.valuation (w.evalAt An.param) = A.valuation c →
                IsLocalRing.residue A ⟨c⁻¹ * w.evalAt An.param, h'⟩ = IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩ → f ∈ w.toValuationSubring) →
            ∃ (hm : (res ⟨f, hf⟩ : RatFunc (IsLocalRing.ResidueField A)) ∈ (placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)).toValuationSubring)
              (hv : P.evalAt f ∈ A),
              algebraMap (IsLocalRing.ResidueField A) (placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)).ResidueField
                  (IsLocalRing.residue A ⟨P.evalAt f, hv⟩) =
                IsLocalRing.residue (placeOfPoint (IsLocalRing.ResidueField A) (IsLocalRing.residue A ⟨c⁻¹ * P.evalAt An.param, h⟩)).toValuationSubring ⟨res ⟨f, hf⟩, hm⟩) := by sorry
