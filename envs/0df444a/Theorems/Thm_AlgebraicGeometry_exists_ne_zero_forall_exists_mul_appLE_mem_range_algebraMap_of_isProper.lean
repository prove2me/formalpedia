-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper
-- name    : AlgebraicGeometry.exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/befd7974-0a5e-5886-8d5d-81391e4e44c1
-- title:
--   Properness gives a uniform denominator for L-valued points
-- statement:
--   Let $R$ be a commutative integral domain and $K$ a field which is an $R$-algebra and a fraction field of $R$ (both in universe $u$). Let $X$ be a scheme and $f \colon X \to \operatorname{Spec} K$ a morphism which is proper, let $(U_i)_{i \in \iota}$ be a family of open subschemes of $X$ indexed by an arbitrary type $\iota$ whose supremum is $\top$, i.e. which covers $X$, and for each $i$ let $s_i$ be a finite subset of $\Gamma(X, U_i)$. The assertion is that there exists $c \in R$, $c \neq 0$, such that the following holds for every valuation ring $V$ which is an integral domain and an $R$-algebra, every field $L$ which is a $V$-algebra and a fraction field of $V$, equipped with $R$- and $K$-algebra structures making $R \to V \to L$ and $R \to K \to L$ commute with $R \to L$, and every morphism $a \colon \operatorname{Spec} L \to X$ satisfying $a$ followed by $f$ equal to $\operatorname{Spec}$ of $\operatorname{algebraMap} K L$: there is an index $i$ with $\top \le a^{-1}(U_i)$, that is, $a$ factors through $U_i$, and for every $g \in s_i$ the product of the image of $c$ in $L$ with the element of $L$ obtained from $g$ via the map $\Gamma(X, U_i) \to \Gamma(\operatorname{Spec} L, \top)$ induced by $a$ and the canonical isomorphism $\Gamma(\operatorname{Spec} L, \top) \cong L$ lies in the image of $V \to L$.
--
--   This is the explicit form of "properness implies boundedness" for a proper $K$-scheme: the coordinates of all $L$-valued points, for $L$ the fraction field of any valuation ring over $R$, admit a single denominator $c \in R \setminus \{0\}$, uniformly in the valued extension, with neither finiteness nor affineness required of the cover. It feeds the construction of finite families of models catching points of index one in the Néron model infrastructure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

theorem AlgebraicGeometry.exists_ne_zero_forall_exists_mul_appLE_mem_range_algebraMap_of_isProper
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]
    {ι : Type v} (U : ι → X.Opens) (hcov : ⨆ i, U i = ⊤) (s : ∀ i, Finset Γ(X, U i)) :
    ∃ c : R, c ≠ 0 ∧
      ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V] [Algebra R V]
        (L : Type u) [Field L] [Algebra V L] [IsFractionRing V L] [Algebra R L] [IsScalarTower R V L]
        [Algebra K L] [IsScalarTower R K L]
        (a : Spec (CommRingCat.of L) ⟶ X), a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)) →
        ∃ (i : ι) (h : ⊤ ≤ a ⁻¹ᵁ U i), ∀ g ∈ s i,
          algebraMap R L c * (Scheme.ΓSpecIso (CommRingCat.of L)).hom (a.appLE (U i) ⊤ h g) ∈
            Set.range (algebraMap V L) := by sorry
