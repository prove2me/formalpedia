-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_idealSheafData_tensor_linearEquiv_of_presentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/8a2be96c-5a4d-5486-93a9-e617e5bf1763
-- title:
--   Invertible sheaf on an integral scheme as fractional ideal
-- statement:
--   Let $X$ be an integral scheme and let $M$ be a sheaf of $\mathcal{O}_X$-modules on $X$ that is invertible in the sense that every point of $X$ has an open neighbourhood $U$ for which the pullback of $M$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit module on $U$. Let $K = K(X)$ be the function field of $X$, and let $\varphi$ assign to each open $U$ an additive map $\varphi_U \colon \Gamma(M,U) \to K$, subject to three hypotheses: $\varphi$ commutes with restriction along inclusions $V \le U$ whenever $V$ is nonempty; $\varphi_U(a \cdot m) = \iota(a)\,\varphi_U(m)$ for nonempty $U$, $a \in \Gamma(X,U)$ and $m \in \Gamma(M,U)$, where $\iota$ is the structure map $\Gamma(X,U) \to K$; and $\varphi_U$ is injective for every nonempty $U$. Then there exist two ideal sheaf data $I$, $J$ on $X$ (quasi-coherent ideals $I(U), J(U) \subseteq \Gamma(X,U)$ on affine opens, compatible with restriction) together with $\Gamma(X,U)$-linear isomorphisms $e_U \colon I(U) \otimes_{\Gamma(X,U)} \Gamma(M,U) \xrightarrow{\sim} J(U)$, indexed by the affine opens $U$, such that: for nonempty affine $U$, $a \in I(U)$ holds exactly when for each $m \in \Gamma(M,U)$ the element $\iota(a)\varphi_U(m)$ of $K$ lies in the image of $\Gamma(X,U)$; $I(U)$ and $J(U)$ are nonzero for every nonempty affine $U$; $\iota(e_U(a \otimes m)) = \iota(a)\,\varphi_U(m)$ in $K$ for nonempty affine $U$; and the $e_U$ commute with restriction along inclusions $V \le U$ of affine opens, the restriction of $a \in I(U)$ being viewed in $I(V)$ via `I.ideal_le_comap_ideal`.
--
--   This is the classical statement that an invertible sheaf on an integral scheme is isomorphic to an invertible fractional ideal, here in the concrete form of an ideal of denominators $I$ and an ideal of numerators $J$ with $I \otimes M \cong J$ on affine opens, naturally in the affine open. It serves the twisting step in the proof that Euler characteristics of tensor powers of an invertible sheaf are polynomial (Snapper's theorem), and is cited by the lemmas producing the exact sequences that compare $\chi(M^{\otimes(n+1)})$ with $\chi(M^{\otimes n})$ modulo sheaves supported on smaller closed subsets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_idealSheafData_tensor_linearEquiv_of_presentation
    {X : Scheme.{u}} [IsIntegral X] (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hφ : (∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U))) :
    ∃ (I J : X.IdealSheafData)
      (e : ∀ U : X.affineOpens, ↥(I.ideal U) ⊗[Γ(X, U)] Γ(M, U) ≃ₗ[Γ(X, U)] ↥(J.ideal U)),
      (∀ (U : X.affineOpens) [Nonempty U] (a : Γ(X, U)),
          a ∈ I.ideal U ↔ ∀ m : Γ(M, U), ∃ b : Γ(X, U),
            algebraMap Γ(X, U) X.functionField b = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.affineOpens, Nonempty U → I.ideal U ≠ ⊥ ∧ J.ideal U ≠ ⊥) ∧
      (∀ (U : X.affineOpens) [Nonempty U] (a : ↥(I.ideal U)) (m : Γ(M, U)),
          algebraMap Γ(X, U) X.functionField (e U (a ⊗ₜ m) : Γ(X, U)) =
            algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ (U V : X.affineOpens) (h : (V : X.Opens) ≤ U) (a : ↥(I.ideal U)) (m : Γ(M, U)),
          X.presheaf.map (homOfLE h).op (e U (a ⊗ₜ m) : Γ(X, U)) =
            e V (⟨X.presheaf.map (homOfLE h).op a, I.ideal_le_comap_ideal h a.2⟩ ⊗ₜ
              M.presheaf.map (homOfLE h).op m)) := by sorry
