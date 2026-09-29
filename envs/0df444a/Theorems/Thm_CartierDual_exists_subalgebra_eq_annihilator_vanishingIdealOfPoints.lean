-- Prove2me | Theorems.Thm_CartierDual_exists_subalgebra_eq_annihilator_vanishingIdealOfPoints
-- name    : CartierDual.exists_subalgebra_eq_annihilator_vanishingIdealOfPoints
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/8dd319f6-d840-5d96-8bd2-dbf032728dd2
-- title:
--   Annihilator of I_S as a Hopf subalgebra of the Cartier dual
-- statement:
--   Let $F$ be a field and $A$ a commutative Hopf algebra over $F$ that is finite as an $F$-module, and let $L$ be a field equipped with an $F$-algebra structure. Let $S$ be a submonoid of the monoid `WithConv (A →ₐ[F] L)` of $F$-algebra maps $A \to L$ under convolution, and write $\mathrm{ptSet}\,S$ for the set of those $\nu : A \to_{\mathrm{alg}} L$ whose class in `WithConv` lies in $S$, $I_S = \{a \in A : \nu(a) = 0 \text{ for all } \nu \in \mathrm{ptSet}\,S\}$ for the associated ideal [`HopfAlgebra.vanishingIdealOfPoints`](def/HopfAlgebra_CharacterClosure.html#L16), and $A/I_S$ for the quotient [`HopfAlgebra.pointQuot S`](def/HopfAlgebra_CharacterClosure.html#L64). Two hypotheses are imposed: (i) the pairs of points of $\mathrm{ptSet}\,S$ separate $(A/I_S) \otimes_F (A/I_S)$, in the sense that an element $x$ of this tensor product with $\mathrm{evalPair}(\mathrm{ptSet}\,S,\nu,\nu')(x) = 0$ for all $\nu, \nu' \in \mathrm{ptSet}\,S$ — where $\mathrm{evalPair}$ is the algebra map $\bar a \otimes \bar b \mapsto \nu(a)\nu'(b)$ obtained from the two factorisations through $A/I_S$ — is zero; and (ii) $\mathrm{ptSet}\,S$ is stable under composition with the antipode: for each $\nu \in \mathrm{ptSet}\,S$ there is $\nu' \in \mathrm{ptSet}\,S$ whose underlying $F$-linear map equals $\nu$ composed after the antipode of $A$. The conclusion asserts the existence of an $F$-subalgebra $B$ of [`CartierDual F A`](def/HopfAlgebra_CartierDual.html#L12) $= \operatorname{Hom}_F(A,F)$ whose underlying set is exactly the annihilator $\{\theta : \theta(a) = 0 \text{ for all } a \in I_S\}$, such that for every $\theta \in B$ the comultiplication $\Delta(\theta)$ lies in the $F$-span of $\{\varphi \otimes_F \psi : \varphi, \psi \in B\}$, and the antipode of [`CartierDual F A`](def/HopfAlgebra_CartierDual.html#L12) maps $B$ into itself.
--
--   This is the Hopf-algebra form of the statement that, for a finite subgroup of points $S$ of $G = \operatorname{Spec} A$ cut out by the ideal $I_S$, the annihilator $I_S^{\perp}$ inside the Cartier dual $A^{\vee}$ is a Hopf subalgebra, namely the functions on $G^{\vee}$ factoring through the dual of the subgroup; the two hypotheses replace the assumption that $S$ is a subgroup scheme. It is used by [`HopfAlgebra.characterGenericFibre_eq_and_isComulStable_and_isAntipodeStable`](thm.html#HopfAlgebra.characterGenericFibre_eq_and_isComulStable_and_isAntipodeStable) in the analysis of finite flat Hopf algebras of multiplicative type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CartierDual_exists_subalgebra_eq_annihilator_vanishingIdealOfPoints.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CharacterClosure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem CartierDual.exists_subalgebra_eq_annihilator_vanishingIdealOfPoints
    (F : Type) [Field F] (A : Type) [CommRing A] [HopfAlgebra F A] [Module.Finite F A]
    (L : Type) [Field L] [Algebra F L]
    (S : Submonoid (WithConv (A →ₐ[F] L)))
    (hsep : ∀ x : TensorProduct F (HopfAlgebra.pointQuot S) (HopfAlgebra.pointQuot S),
      (∀ (ν ν' : A →ₐ[F] L) (hν : ν ∈ HopfAlgebra.ptSet S) (hν' : ν' ∈ HopfAlgebra.ptSet S),
        HopfAlgebra.evalPair (HopfAlgebra.ptSet S) ν ν' hν hν' x = 0) → x = 0)
    (hinv : ∀ ν ∈ HopfAlgebra.ptSet S, ∃ ν' ∈ HopfAlgebra.ptSet S,
      ν'.toLinearMap = ν.toLinearMap ∘ₗ HopfAlgebraStruct.antipode (R := F)) :
    ∃ B : Subalgebra F (CartierDual F A),
      (B : Set (CartierDual F A))
          = {θ | ∀ a ∈ HopfAlgebra.vanishingIdealOfPoints (HopfAlgebra.ptSet S), θ a = 0} ∧
      (∀ θ ∈ B, Coalgebra.comul (R := F) θ
          ∈ Submodule.span F (Set.image2 (fun φ ψ => φ ⊗ₜ[F] ψ) (B : Set (CartierDual F A)) (B : Set (CartierDual F A)))) ∧
      (∀ θ ∈ B, HopfAlgebraStruct.antipode (R := F) (A := CartierDual F A) θ ∈ B) := by sorry
