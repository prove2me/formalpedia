-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_forall_nonempty_pullback_thickening_iso_of_isProper
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_forall_nonempty_pullback_thickening_iso_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/da9db3d9-8629-5ce9-888b-43c4b50ce312
-- title:
--   Fibrewise isomorphic invertible modules are isomorphic over a complete local base
-- statement:
--   Let $R$ be a noetherian local ring that is complete for the adic topology of its maximal ideal $\mathfrak m$, let $X$ be a scheme and $p : X \to \operatorname{Spec} R$ a proper morphism. Suppose given schemes $X_k$ for $k \in \mathbb N$, morphisms $q_k : X_k \to \operatorname{Spec}(R/\mathfrak m^{k+1})$ and $j_k : X_k \to X$ such that each square formed by $j_k$, $q_k$, $p$ and $\operatorname{Spec}$ of the quotient map $R \to R/\mathfrak m^{k+1}$ is cartesian (hypothesis `hj`), and such that for each $k$ the structure map $R/\mathfrak m^{k+1} \to \Gamma(X_k, \top)$, for the $R/\mathfrak m^{k+1}$-algebra structure on global sections induced by $q_k$, is bijective (hypothesis `hH0`). Let $\mathcal M, \mathcal M'$ be sheaves of modules on $X$ that are invertible in the sense that every point of $X$ has an open neighbourhood $U$ whose pullback along the inclusion $U \hookrightarrow X$ is isomorphic to the unit module of the sheaf of rings of $U$. Assume that for every $k$ the pullbacks $j_k^{*}\mathcal M$ and $j_k^{*}\mathcal M'$ are isomorphic, with no compatibility between these isomorphisms for varying $k$ required. Then $\mathcal M$ and $\mathcal M'$ are isomorphic as modules on $X$.
--
--   This is the statement that an invertible module on a proper scheme over a complete local noetherian ring is determined by its restrictions to the infinitesimal thickenings of the closed fibre, even when the fibrewise isomorphisms are given incoherently; it combines the normalisation of trivialisations along the tower with the full faithfulness half of Grothendieck's existence theorem in formal geometry. It is used in the study of line bundles and Rosati compatibility on fake elliptic curves in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_of_forall_nonempty_pullback_thickening_iso_of_isProper.lean

import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_forall_nonempty_pullback_thickening_iso_of_isProper
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (Xk : ℕ → Scheme.{u})
    (q : ∀ k : ℕ, Xk k ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))
    (j : ∀ k : ℕ, Xk k ⟶ X)
    (hj : ∀ k : ℕ, IsPullback (j k) (q k) p
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (k + 1))))))
    (hH0 : ∀ k : ℕ,
      letI := Scheme.TwoAffineOpenCover.algebraOfHom (q k) ⊤
      Function.Bijective (algebraMap (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)) Γ(Xk k, ⊤)))
    (𝓜 𝓜' : X.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (h𝓜' : Scheme.Modules.IsInvertible 𝓜')
    (hk : ∀ k : ℕ, Nonempty ((Scheme.Modules.pullback (j k)).obj 𝓜 ≅ (Scheme.Modules.pullback (j k)).obj 𝓜')) :
    Nonempty (𝓜 ≅ 𝓜') := by sorry
