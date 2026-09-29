-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective
-- name    : AlgebraicGeometry.OModulePresheaf.exists_chartModel_extPushout_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/75a7cf44-ad71-57fa-b3df-3f809b75efe8
-- title:
--   Push-out chart models over affine opens of a chart
-- statement:
--   Let $A$ be a commutative ring, let $P$ be a locally Noetherian scheme and let $q : P \to \operatorname{Spec} A$. Let $G_E$ and $G_K$ be `OModulePresheaf` data for $q$, i.e. assignments $U \mapsto G(U)$ of an $A$-module that is also a $\Gamma(P,U)$-module compatibly with the $A$-algebra structure on $\Gamma(P,U)$ induced by $q$, together with $A$-linear restrictions $G.\mathrm{res}$ that are semilinear over the presheaf restrictions and satisfy the identity and composition laws. Both are assumed coherent (each $G(U)$ is a finite $\Gamma(P,U)$-module for $U$ affine open) and quasi-coherent (for $U$ affine open and $f \in \Gamma(P,U)$, every section over $P_f := P.\mathrm{basicOpen}\, f$ becomes, after multiplication by some $f^n$, the restriction of a section over $U$, and any section over $U$ restricting to $0$ on $P_f$ is killed by some $f^n$). Let $U_0$ be an affine open, $r \in \mathbb{N}$, $pr : \Gamma(P,U_0)^r \to G_E(U_0)$ a surjective $\Gamma(P,U_0)$-linear map and $\delta : \ker pr \to G_K(U_0)$ linear. The conclusion asserts the existence, indexed by the affine opens $U \subseteq U_0$, of: linear maps $pr_U : \Gamma(P,U)^r \to G_E(U)$ which are surjective, agree with $pr$ after coordinatewise restriction, and are compatible with further restriction; maps $g_U : \ker pr \to \ker pr_U$ given coordinatewise by restriction; linear maps $\delta_U : \ker pr_U \to G_K(U)$ with $\delta_U(g_U s) = \delta(s)|_U$, such that the image of $g_U$ spans $\ker pr_U$ over $\Gamma(P,U)$ and $\delta_{U'}(s') = \delta_U(s)|_{U'}$ whenever $s'$ has coordinates the restrictions of those of $s$. Moreover, equipping $M(U) := \mathrm{ExtPushout}(pr_U, \delta_U) = (G_K(U) \times \Gamma(P,U)^r)/\{(\delta s, -s) : s \in \ker pr_U\}$ with the $A$-module structure coming from $\Gamma(P,U)$, there exist the corresponding scalar-tower compatibilities, $A$-linear restriction maps $\mathrm{res}_{U' \le U} : M(U) \to M(U')$ semilinear over presheaf restriction and satisfying the identity and composition laws, the two quasi-coherence conditions for $M$ on basic opens $U_g = P.\mathrm{basicOpen}\, g$ inside $U$, finiteness of $M(U)$ over $\Gamma(P,U)$, and $A$-linear maps $\vartheta_U : G_K(U) \to M(U)$ and $\theta_{E,U} : M(U) \to G_E(U)$ which are $\Gamma(P,U)$-homogeneous, commute with restriction, and form a short exact sequence ($\vartheta_U$ injective, $\operatorname{range} \vartheta_U = \ker \theta_{E,U}$, $\theta_{E,U}$ surjective); finally $\vartheta_U = \mathrm{inl}$, $\theta_{E,U} = \mathrm{proj}$, and the restriction maps carry $\mathrm{inl}\, n$ to $\mathrm{inl}(n|_{U'})$ and $\mathrm{inr}\, v$ to $\mathrm{inr}$ of the coordinatewise restriction of $v$.
--
--   This is the one-chart step in the construction of a coherent quasi-coherent extension of $G_E$ by $G_K$ from local presentation data: a chosen presentation of $G_E(U_0)$ together with a cocycle-like map $\delta$ on its relations is spread over all affine opens inside $U_0$ by flat base change, and the resulting push-out modules are assembled into module data with functorial, quasi-coherent restrictions. It is used by [`AlgebraicGeometry.OModulePresheaf.exists_chartModels_extPushout_of_forall_res_symm_mk_eq`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_chartModels_extPushout_of_forall_res_symm_mk_eq), which glues such chart models over a two-chart affine cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_chartModel_extPushout_of_surjective.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_LinearMap_ExtPushout

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_chartModel_extPushout_of_surjective
    {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsLocallyNoetherian P]
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (U₀ : P.Opens) (hU₀ : IsAffineOpen U₀) (r : ℕ)
    (pr : (Fin r → Γ(P, U₀)) →ₗ[Γ(P, U₀)] GE.obj U₀) (hpr : Function.Surjective pr)
    (δ : ↥(LinearMap.ker pr) →ₗ[Γ(P, U₀)] GK.obj U₀) :
    ∃ (prU : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}),
        (Fin r → Γ(P, U.1.1)) →ₗ[Γ(P, U.1.1)] GE.obj U.1.1)
      (_hprU : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (v : Fin r → Γ(P, U₀)),
        prU U (fun m => (P.presheaf.map (homOfLE U.2).op).hom (v m)) = GE.res U.2 (pr v))
      (_hprUs : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), Function.Surjective (prU U))
      (_hprUn : ∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (v : Fin r → Γ(P, U.1.1)),
        prU U' (fun m => (P.presheaf.map (homOfLE h).op).hom (v m)) = GE.res h (prU U v))
      (gU : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), ↥(LinearMap.ker pr) → ↥(LinearMap.ker (prU U)))
      (_hgU : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (s : ↥(LinearMap.ker pr)) (m : Fin r),
        ((gU U s : ↥(LinearMap.ker (prU U))) : Fin r → Γ(P, U.1.1)) m =
          (P.presheaf.map (homOfLE U.2).op).hom ((s : Fin r → Γ(P, U₀)) m))
      (δU : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), ↥(LinearMap.ker (prU U)) →ₗ[Γ(P, U.1.1)] GK.obj U.1.1)
      (_hδU : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (s : ↥(LinearMap.ker pr)),
        δU U (gU U s) = GK.res U.2 (δ s))
      (_hgUspan : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}),
        Submodule.span Γ(P, U.1.1)
            (Set.range fun s : ↥(LinearMap.ker pr) =>
              ((gU U s : ↥(LinearMap.ker (prU U))) : Fin r → Γ(P, U.1.1))) =
          LinearMap.ker (prU U))
      (_hδUn : ∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1)
        (s : ↥(LinearMap.ker (prU U))) (s' : ↥(LinearMap.ker (prU U'))),
        (∀ m : Fin r, (s' : Fin r → Γ(P, U'.1.1)) m = (P.presheaf.map (homOfLE h).op).hom ((s : Fin r → Γ(P, U.1.1)) m)) →
        δU U' s' = GK.res h (δU U s)),
    letI : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), Module A (LinearMap.ExtPushout (prU U) (δU U)) :=
      fun U => Module.compHom _ (Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1).algebraMap
    ∃ (_ : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}),
          letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1
          IsScalarTower A Γ(P, U.1.1) (LinearMap.ExtPushout (prU U) (δU U)))
      (res : ∀ {U U' : {U : P.affineOpens // U.1 ≤ U₀}}, U'.1.1 ≤ U.1.1 → (LinearMap.ExtPushout (prU U) (δU U) →ₗ[A] LinearMap.ExtPushout (prU U') (δU U')))
      (res_smul : ∀ {U U' : {U : P.affineOpens // U.1 ≤ U₀}} (h : U'.1.1 ≤ U.1.1) (a : Γ(P, U.1.1)) (x : LinearMap.ExtPushout (prU U) (δU U)),
          res h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res h x)
      (res_refl : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (x : LinearMap.ExtPushout (prU U) (δU U)), res (le_refl U.1.1) x = x)
      (res_comp : ∀ {U U' U'' : {U : P.affineOpens // U.1 ≤ U₀}} (h : U''.1.1 ≤ U'.1.1) (h' : U'.1.1 ≤ U.1.1)
          (x : LinearMap.ExtPushout (prU U) (δU U)), res (h.trans h') x = res h (res h' x))
      (hqc : ∀ (U Ug : {U : P.affineOpens // U.1 ≤ U₀}) (g : Γ(P, U.1.1)) (hUg : Ug.1.1 = P.basicOpen g),
          (∀ y : LinearMap.ExtPushout (prU Ug) (δU Ug), ∃ (n : ℕ) (x : LinearMap.ExtPushout (prU U) (δU U)),
              res (hUg.trans_le (P.basicOpen_le g)) x =
                (P.presheaf.map (homOfLE (hUg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
          (∀ x : LinearMap.ExtPushout (prU U) (δU U), res (hUg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
      (hfg : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), Module.Finite (Γ(P, U.1.1) : Type u) (LinearMap.ExtPushout (prU U) (δU U)))
      (ϑ : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), GK.obj U.1.1 →ₗ[A] LinearMap.ExtPushout (prU U) (δU U))
      (θE : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), LinearMap.ExtPushout (prU U) (δU U) →ₗ[A] GE.obj U.1.1)
            (hϑs : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ U (a • x) = a • ϑ U x)
      (hθEs : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (a : Γ(P, U.1.1)) (x : LinearMap.ExtPushout (prU U) (δU U)), θE U (a • x) = a • θE U x)
            (hϑn : ∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (x : GK.obj U.1.1),
          ϑ U' (GK.res h x) = res h (ϑ U x))
      (hθEn : ∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (x : LinearMap.ExtPushout (prU U) (δU U)),
          θE U' (res h x) = GE.res h (θE U x))
            (hexact : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), LinearMap.range (ϑ U) = LinearMap.ker (θE U))
      (hsurj : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), Function.Surjective (θE U))
      (hϑi : ∀ (U : {U : P.affineOpens // U.1 ≤ U₀}), Function.Injective (ϑ U)),

      (∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (x : GK.obj U.1.1),
        ϑ U x = LinearMap.ExtPushout.inl (prU U) (δU U) x) ∧
      (∀ (U : {U : P.affineOpens // U.1 ≤ U₀}) (x : LinearMap.ExtPushout (prU U) (δU U)),
        θE U x = LinearMap.ExtPushout.proj (prU U) (δU U) x) ∧
      (∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (n : GK.obj U.1.1),
        res h (LinearMap.ExtPushout.inl (prU U) (δU U) n) = LinearMap.ExtPushout.inl (prU U') (δU U') (GK.res h n)) ∧
      (∀ (U U' : {U : P.affineOpens // U.1 ≤ U₀}) (h : U'.1.1 ≤ U.1.1) (v : Fin r → Γ(P, U.1.1)),
        res h (LinearMap.ExtPushout.inr (prU U) (δU U) v) =
          LinearMap.ExtPushout.inr (prU U') (δU U') (fun m => (P.presheaf.map (homOfLE h).op).hom (v m))) := by sorry
