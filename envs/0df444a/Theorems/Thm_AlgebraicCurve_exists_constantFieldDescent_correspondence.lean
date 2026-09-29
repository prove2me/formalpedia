-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_constantFieldDescent_correspondence
-- name    : AlgebraicCurve.exists_constantFieldDescent_correspondence
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/d4cd656a-22f1-5ddf-800f-25c5dcc847ad
-- title:
--   Lefschetz principle: descent of a curve with finitely many correspondences
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$ and $F$ a field extension of $K$ which is a curve over $K$ in the project's sense: every nonzero $f \in F$ has a degree-zero divisor whose local order at each place $v$ of $F/K$ is $\mathrm{ord}_v(f)$, every such place has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank $1$ over $F$. Assume moreover that $F$ contains an element $x$ transcendental over $K$ with $F$ finite over $K(x)$. Let $\iota$ be a finite index type and, for each $i$, let $F'_i$ be a field extension of $K$ equipped with two $K$-algebra maps $\varphi_i, \psi_i \colon F \to F'_i$, such that each $\varphi_i$ is integral as a ring map and each $F'_i$ is a finite module over $F$ via $\psi_i$. Then there exist a countable algebraically closed field $K_0$ with $K$-algebra and $\mathbb{C}$-algebra structures over it (i.e. embeddings $K_0 \hookrightarrow K$, $K_0 \hookrightarrow \mathbb{C}$), a field $F_0$ with $K_0 \subseteq F_0 \subseteq F$ and $F'_{0,i}$ with $K_0 \subseteq F'_{0,i} \subseteq F'_i$, all compatible as scalar towers over $K_0$, such that $F_0$ is a curve over $K_0$ and each $F'_{0,i}$ is a curve over $K_0$, each of $F_0$ and $F'_{0,i}$ contains an element transcendental over $K_0$ over which it is finite, the image of $F_0$ generates $F$ over $K$ and the image of $F'_{0,i}$ generates $F'_i$ over $K$, and there are $K_0$-algebra maps $\varphi_{0,i}, \psi_{0,i} \colon F_0 \to F'_{0,i}$ along which $F'_{0,i}$ is a finite $F_0$-module and which are compatible with $\varphi_i, \psi_i$ on the image of $F_0$ in $F$.
--
--   This is the descent half of the Lefschetz principle for a curve equipped with finitely many correspondences: the curve, the correspondence curves and both projections are all defined over a countable algebraically closed subfield of $K$ that embeds into $\mathbb{C}$. It is used to reduce statements about correspondences over an arbitrary algebraically closed field of characteristic $0$ to the complex case, in [`AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero`](thm.html#AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero) and in [`AlgebraicCurve.exists_int_matrix_forall_toMatrix_tateModule_rep_correspondence_eq_map`](thm.html#AlgebraicCurve.exists_int_matrix_forall_toMatrix_tateModule_rep_correspondence_eq_map).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_constantFieldDescent_correspondence.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

universe u v w x

theorem AlgebraicCurve.exists_constantFieldDescent_correspondence
    (K : Type u) (F : Type v) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {ι : Type w} [Finite ι] (F' : ι → Type x) [∀ i, Field (F' i)] [∀ i, Algebra K (F' i)]
    (φ ψ : ∀ i, F →ₐ[K] F' i)
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral) (hfin : ∀ i, FiniteAlong K (ψ i)) :
    ∃ (K₀ : Type u) (F₀ : Type v) (F'₀ : ι → Type x)
      (_ : Field K₀) (_ : Field F₀) (_ : ∀ i, Field (F'₀ i))
      (_ : Algebra K₀ K) (_ : Algebra K₀ ℂ) (_ : IsAlgClosed K₀) (_ : Countable K₀)
      (_ : Algebra K₀ F₀) (_ : Algebra F₀ F) (_ : Algebra K₀ F)
      (_ : IsScalarTower K₀ K F) (_ : IsScalarTower K₀ F₀ F) (_ : IsCurveOver K₀ F₀)
      (_ : ∀ i, Algebra K₀ (F'₀ i)) (_ : ∀ i, Algebra (F'₀ i) (F' i)) (_ : ∀ i, Algebra K₀ (F' i))
      (_ : ∀ i, IsScalarTower K₀ K (F' i)) (_ : ∀ i, IsScalarTower K₀ (F'₀ i) (F' i))
      (_ : ∀ i, IsCurveOver K₀ (F'₀ i))
      (φ₀ ψ₀ : ∀ i, F₀ →ₐ[K₀] F'₀ i),
      (∃ x : F₀, Transcendental K₀ x ∧
        FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set F₀)) F₀) ∧
      IntermediateField.adjoin K (Set.range (algebraMap F₀ F)) = ⊤ ∧
      (∀ i, ∃ x : F'₀ i, Transcendental K₀ x ∧
        FiniteDimensional (IntermediateField.adjoin K₀ ({x} : Set (F'₀ i))) (F'₀ i)) ∧
      (∀ i, IntermediateField.adjoin K (Set.range (algebraMap (F'₀ i) (F' i))) = ⊤) ∧
      (∀ i (f : F₀), φ i (algebraMap F₀ F f) = algebraMap (F'₀ i) (F' i) (φ₀ i f)) ∧
      (∀ i (f : F₀), ψ i (algebraMap F₀ F f) = algebraMap (F'₀ i) (F' i) (ψ₀ i f)) ∧
      (∀ i, FiniteAlong K₀ (φ₀ i)) ∧ (∀ i, FiniteAlong K₀ (ψ₀ i)) := by sorry
