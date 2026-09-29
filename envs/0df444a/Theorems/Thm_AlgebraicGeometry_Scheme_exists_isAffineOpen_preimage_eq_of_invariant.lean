-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_isAffineOpen_preimage_eq_of_invariant
-- name    : AlgebraicGeometry.Scheme.exists_isAffineOpen_preimage_eq_of_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/53679272-f38e-58c0-9930-0f58dea1ef00
-- title:
--   Invariant affine opens descend along a finite flat quotient
-- statement:
--   Let $X$, $R$, $Y$ be schemes (in a fixed universe), and let $s, t \colon R \to X$ be morphisms, each finite, flat and locally of finite presentation. Assume $(s,t)$ is jointly monomorphic, i.e. for all schemes $T$ and all $a, b \colon T \to R$ with $a \mathbin{;} s = b \mathbin{;} s$ and $a \mathbin{;} t = b \mathbin{;} t$ one has $a = b$; and assume that for every scheme $T$ the relation on $T$-points of $X$ given by $x \sim y$ iff there exists $\varphi \colon T \to R$ with $\varphi \mathbin{;} s = x$ and $\varphi \mathbin{;} t = y$ is an equivalence relation. Let $p \colon X \to Y$ be a morphism, finite, flat, locally of finite presentation and surjective, with $s \mathbin{;} p = t \mathbin{;} p$, and assume the square formed by $s$, $t$ and the two copies of $p$ is cartesian, so that $(s,t)$ is the kernel pair of $p$ and $R \cong X \times_Y X$. Finally let $W$ be an open subscheme of $X$ which is affine and invariant, in the sense that the open preimages satisfy $s^{-1}(W) = t^{-1}(W)$. Then there exists an open $V \subseteq Y$ which is affine and satisfies $p^{-1}(V) = W$.
--
--   This is the descent statement that an invariant affine open of $X$ is exactly the preimage of an affine open of the quotient $Y = X/R$, for $R$ a finite locally free equivalence relation; it is the local step used to build affine charts on such quotients. It is cited in the construction of affine opens of $Y$ containing a prescribed set of points whose $p$-preimages lie in a given invariant open.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_isAffineOpen_preimage_eq_of_invariant.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.exists_isAffineOpen_preimage_eq_of_invariant
    {X R Y : Scheme.{u}} (s t : R ⟶ X)
    [IsFinite s] [Flat s] [LocallyOfFinitePresentation s]
    [IsFinite t] [Flat t] [LocallyOfFinitePresentation t]
    (hmono : ∀ {T : Scheme.{u}} (a b : T ⟶ R), a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b)
    (hequiv : ∀ T : Scheme.{u},
      _root_.Equivalence fun x y : T ⟶ X => ∃ φ : T ⟶ R, φ ≫ s = x ∧ φ ≫ t = y)
    (p : X ⟶ Y) (w : s ≫ p = t ≫ p)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (hR : IsPullback s t p p) (W : X.Opens) (hW : IsAffineOpen W) (hinv : s ⁻¹ᵁ W = t ⁻¹ᵁ W) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ p ⁻¹ᵁ V = W := by sorry
