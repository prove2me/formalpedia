-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableModel_finrank_kaehlerDifferential_eq_of_smoothOfRelativeDimension
-- name    : AlgebraicCurve.SemistableModel.finrank_kaehlerDifferential_eq_of_smoothOfRelativeDimension
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/0d085709-c26b-5bcc-a2af-e3a2f67fdd86
-- title:
--   Relative dimension n forces dim_F Ω_{F/L} = n
-- statement:
--   Let $A$ be a commutative domain with a field of fractions $L$ (that is, $L$ is an $A$-algebra which is a fraction ring of $A$), and let $F$ be a field equipped with an $L$-algebra structure. Let $X$ be an integral scheme (in the universe of types of size $0$) and let $\mathrm{toBase} \colon X \to \operatorname{Spec} A$ be a morphism of schemes. Let $\varphi \colon F \to X.\mathrm{functionField}$ be a ring isomorphism of $F$ with the function field of $X$ (the stalk of $\mathcal{O}_X$ at the generic point), and assume the compatibility that for every $a \in A$ the element $\varphi(\mathrm{algebraMap}_{L,F}(\mathrm{algebraMap}_{A,L}(a)))$ equals the image of $a$ under `SemistableModel.baseToFunctionField toBase`, i.e. under the composite $A \to \Gamma(X,\mathcal O_X) \to \mathcal O_{X,\eta}$ obtained from the inverse of the global-sections isomorphism for $\operatorname{Spec} A$, the map on global sections induced by $\mathrm{toBase}$, and the germ map at the generic point. Let $W$ be an open subscheme of $X$ whose underlying set is nonempty, let $n$ be a natural number, and assume that the open immersion $W.\iota$ followed by $\mathrm{toBase}$ is smooth of relative dimension $n$. Then the module of Kähler differentials $\Omega_{F/L}$ is a finite $F$-module and its $F$-rank equals $n$.
--
--   This identifies the transcendence-theoretic invariant $\dim_F \Omega_{F/L}$ of the function field of an integral $A$-scheme with the relative dimension of any nonempty smooth open of that scheme; for $n = 1$ it says that $F$ is a function field of one variable over $L$. It is used in the analysis of the smooth locus of a semistable model, for instance in the statements about the stalks at points of the smooth locus being regular of the expected shape (generation of the maximal ideal by two elements, and principality or discreteness of the valuation on suitable quotients).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableModel_finrank_kaehlerDifferential_eq_of_smoothOfRelativeDimension.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.SemistableModel.finrank_kaehlerDifferential_eq_of_smoothOfRelativeDimension
    {A : Type} [CommRing A] [IsDomain A] {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
    {F : Type} [Field F] [Algebra L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of A)) [IsIntegral X]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : A, φ (algebraMap L F (algebraMap A L a)) = SemistableModel.baseToFunctionField toBase a)
    (W : X.Opens) (hW : (W : Set X).Nonempty) (n : ℕ) [SmoothOfRelativeDimension n (W.ι ≫ toBase)] :
    Module.Finite F (KaehlerDifferential L F) ∧ Module.finrank F (KaehlerDifferential L F) = n := by sorry
