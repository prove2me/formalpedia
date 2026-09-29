-- Prove2me | Theorems.Thm_AlgebraicCurve_existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed
-- name    : AlgebraicCurve.existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/95e64d4c-0764-504e-9973-8f13aa042807
-- title:
--   Places and points of a normal proper model
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring satisfying two conditions: for all $a, b \in A$ with $a$ in the maximal ideal of $A$ and $b \neq 0$ there is $n \in \mathbb{N}$ with $b \mid a^{n}$ (a rank-one condition), and $A \neq L$ as a subset. Let $F$ be a field extension of $L$ with `IsCurveOver L F` — every nonzero $f \in F$ admits a divisor of degree $0$ whose value at each place is $\operatorname{ord}_v f$, each place of $F/L$ has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank $1$ over $F$ — and with $F$ of essentially finite type over $L$. Let $X$ be an integral scheme and $\mathrm{toBase} : X \to \operatorname{Spec} A$ a proper morphism such that every stalk of $X$ is integrally closed, and let $\varphi : F \xrightarrow{\sim} K(X)$ be a ring isomorphism onto the function field with $\varphi(a) = \mathrm{toBase}^{\ast}(a)$ for all $a \in A$, where the right-hand side is the composite $A \to \Gamma(X) \to \mathcal{O}_{X,\eta}$. Let $P$ be a place of $F/L$, i.e. a valuation subring of $F$ which contains the image of $L$, is not all of $F$, and is a principal ideal ring. Writing $\mathcal{O}_{X,y} \subseteq F$ for the image under $\varphi^{-1}$ of the stalk at $y$ inside $K(X)$, the assertion is that there is a point $\mathrm{pt} \in X$ with $\mathcal{O}_{X,\mathrm{pt}} = P$ as subrings of $F$; that $\mathrm{pt}$ is the only point of $X$ with this property; that $\mathrm{toBase}(\mathrm{pt})$ is the generic point of $\operatorname{Spec} A$; and that there exists $x \in X$ with $\mathrm{pt} \rightsquigarrow x$, $x \neq \mathrm{pt}$, $\mathrm{toBase}(x)$ the closed point of $\operatorname{Spec} A$, $x$ a closed point of $X$, and $\{ \mathrm{pt}, x \}$ exactly the set of specialisations of $\mathrm{pt}$, such that every $f \in \mathcal{O}_{X,x}$ lies in $P$, has value $P.\mathrm{evalAt}\, f \in A$ (the value being the residue of $f$ in the residue field of $P$ pulled back to $L$ along $L \to \kappa(P)$), and is a unit in $\mathcal{O}_{X,x}$ if and only if that value is a unit of $A$; moreover $x$ is the unique closed point over the closed point of $\operatorname{Spec} A$ whose local ring has this property. Finally, every $y \in X$ lying over the generic point of $\operatorname{Spec} A$ and distinct from the generic point of $X$ satisfies $\mathcal{O}_{X,y} = P'$ for some place $P'$ of $F/L$.
--
--   This is the generic-fibre half of the dictionary between places of $F/L$ and points of a normal proper model $X \to \operatorname{Spec} A$: closed points of the generic fibre correspond bijectively to places, each specialising to exactly one point, a closed point of the special fibre, whose local ring is carried into $A$ by evaluation at the place. It is obtained from the valuative criterion of properness applied to the composite valuation ring $\{f : f(P) \in A\}$, with uniqueness from separatedness, and it supplies the fields `pt`, `localRing_pt` and `toBase_pt` of a `SemistableModel`; the semistable-model descent theorems for modular curves at full level cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed.lean

import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase]

    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (P : Place L F) :
    ∃ pt : X,
      SemistableModel.localRing X φ pt = P.toValuationSubring.toSubring ∧
      (∀ pt' : X, SemistableModel.localRing X φ pt' = P.toValuationSubring.toSubring → pt' = pt) ∧
      (toBase.base pt).asIdeal = ⊥ ∧
      ∃ x : X, pt ⤳ x ∧ x ≠ pt ∧ toBase.base x = closedPoint ↥A ∧ (∀ y : X, x ⤳ y → y = x) ∧
        (∀ y : X, pt ⤳ y → y = pt ∨ y = x) ∧
        (∀ f : F, f ∈ SemistableModel.localRing X φ x →
          f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
            (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ SemistableModel.localRing X φ x, f * g = 1)) ∧

        (∀ x' : X, toBase.base x' = closedPoint ↥A → (∀ y : X, x' ⤳ y → y = x') →
          (∀ f : F, f ∈ SemistableModel.localRing X φ x' →
            f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
              (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ SemistableModel.localRing X φ x', f * g = 1)) → x' = x) ∧

        (∀ y : X, (toBase.base y).asIdeal = ⊥ → y ≠ genericPoint X →
          ∃ P' : Place L F, SemistableModel.localRing X φ y = P'.toValuationSubring.toSubring) := by sorry
