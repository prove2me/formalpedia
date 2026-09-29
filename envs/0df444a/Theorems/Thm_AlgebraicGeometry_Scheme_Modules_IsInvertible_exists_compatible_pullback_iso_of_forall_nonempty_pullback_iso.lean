-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_compatible_pullback_iso_of_forall_nonempty_pullback_iso
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_compatible_pullback_iso_of_forall_nonempty_pullback_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/452a1cbc-5158-5b3f-ab01-359fe590baf9
-- title:
--   Compatible levelwise isomorphisms along a tower of thickenings
-- statement:
--   Let $R$ be a commutative local ring with maximal ideal $\mathfrak m$, let $X$ be a scheme, and let $X_k$ ($k \in \mathbb N$) be schemes equipped with morphisms $q_k \colon X_k \to \operatorname{Spec}(R/\mathfrak m^{k+1})$, morphisms $j_k \colon X_k \to X$ and transition morphisms $t_k \colon X_k \to X_{k+1}$ satisfying $j_{k+1} \circ t_k = j_k$ and $q_{k+1} \circ t_k = \operatorname{Spec}(R/\mathfrak m^{k+2} \to R/\mathfrak m^{k+1}) \circ q_k$, the latter map being the canonical factorisation of quotients coming from $\mathfrak m^{k+2} \subseteq \mathfrak m^{k+1}$. Assume that for each $k$ the structure map $R/\mathfrak m^{k+1} \to \Gamma(X_k, \top)$, for the algebra structure induced by $q_k$, is bijective. Let $\mathcal M, \mathcal M'$ be $\mathcal O_X$-modules that are invertible in the sense that every point of $X$ has an open neighbourhood $U$ on which the pullback along $U \hookrightarrow X$ is isomorphic to the unit module on $U$, and suppose that $j_k^*\mathcal M \cong j_k^*\mathcal M'$ for every $k$. Then there is a family of isomorphisms $\varphi_k \colon j_k^*\mathcal M \cong j_k^*\mathcal M'$ which is compatible with the tower: for every $k$, $\varphi_k$ equals $t_k^*\varphi_{k+1}$ conjugated by the canonical isomorphisms $t_k^* j_{k+1}^* \cong j_k^*$ on $\mathcal M$ and on $\mathcal M'$ furnished by `Scheme.Modules.pullbackComp` and `Scheme.Modules.pullbackCongr`.
--
--   This is the coherence step which upgrades a collection of unrelated isomorphisms between the restrictions of two invertible modules to the successive thickenings $X_k$ into an isomorphism of inverse systems, the obstruction at each stage being an automorphism of an invertible module, that is, a global unit on $X_k$, which lifts along the surjection $R/\mathfrak m^{k+2} \to R/\mathfrak m^{k+1}$. It is used in the proof that two invertible modules with isomorphic restrictions to all thickenings of a proper scheme are isomorphic, via [`AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_forall_nonempty_pullback_thickening_iso_of_isProper`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_forall_nonempty_pullback_thickening_iso_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_compatible_pullback_iso_of_forall_nonempty_pullback_iso.lean

import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_compatible_pullback_iso_of_forall_nonempty_pullback_iso
    (R : Type u) [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (Xk : ℕ → Scheme.{u})
    (q : ∀ k : ℕ, Xk k ⟶ Spec (CommRingCat.of (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1))))
    (j : ∀ k : ℕ, Xk k ⟶ X) (t : ∀ k : ℕ, Xk k ⟶ Xk (k + 1))
    (ht : ∀ k, t k ≫ j (k + 1) = j k)
    (htq : ∀ k, t k ≫ q (k + 1) = q k ≫ Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (k + 1)) :
        IsLocalRing.maximalIdeal R ^ (k + 1 + 1) ≤ IsLocalRing.maximalIdeal R ^ (k + 1)))))
    (hH0 : ∀ k : ℕ,
      letI := Scheme.TwoAffineOpenCover.algebraOfHom (q k) ⊤
      Function.Bijective (algebraMap (R ⧸ IsLocalRing.maximalIdeal R ^ (k + 1)) Γ(Xk k, ⊤)))
    (𝓜 𝓜' : X.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (h𝓜' : Scheme.Modules.IsInvertible 𝓜')
    (hk : ∀ k : ℕ, Nonempty ((Scheme.Modules.pullback (j k)).obj 𝓜 ≅ (Scheme.Modules.pullback (j k)).obj 𝓜')) :
    ∃ φ : ∀ k : ℕ, (Scheme.Modules.pullback (j k)).obj 𝓜 ≅ (Scheme.Modules.pullback (j k)).obj 𝓜',
      ∀ k, φ k = ((Scheme.Modules.pullbackComp (t k) (j (k + 1))).app 𝓜 ≪≫ (Scheme.Modules.pullbackCongr (ht k)).app 𝓜).symm
          ≪≫ (Scheme.Modules.pullback (t k)).mapIso (φ (k + 1))
          ≪≫ ((Scheme.Modules.pullbackComp (t k) (j (k + 1))).app 𝓜' ≪≫ (Scheme.Modules.pullbackCongr (ht k)).app 𝓜') := by sorry
