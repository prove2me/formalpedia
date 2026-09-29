-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq
-- name    : AlgebraicGeometry.OModulePresheaf.exists_overlapIso_extPushout_of_forall_res_symm_mk_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/e163887d-3274-5859-9f28-e799159fcfa4
-- title:
--   Overlap isomorphisms of push-out models on a separated scheme
-- statement:
--   Let $A$ be a commutative ring and $q : P \to \operatorname{Spec} A$ a morphism with $P$ locally Noetherian and $q$ separated. Let $GE$, $GK$, $X$ be $\mathcal O$-module presheaves relative to $q$ (for each open $U$ a module over $A$ and over $\Gamma(P,U)$, with compatible $A$-linear restriction maps, semilinear for restriction of functions), each assumed coherent (finitely generated sections over every affine open) and quasicoherent (the two basic-open conditions of `IsQuasicoherent`). Assume given, for every affine open $W$ and every surjective $\Gamma(P,W)$-linear $p : \Gamma(P,W)^r \to GE(W)$, an isomorphism $\varepsilon_{W,p} : X(W) \cong \operatorname{Hom}_{\Gamma(P,W)}(\ker p, GK(W)) / \operatorname{im}(\text{precomposition with } \ker p \hookrightarrow \Gamma(P,W)^r)$, and that these are compatible with restriction in the following sense: for affine opens $W' \le W$, surjective presentations $p$, $p'$ of ranks $r$, $r'$ over $W$, $W'$, an additive $g : \Gamma(P,W)^r \to \Gamma(P,W')^{r'}$ semilinear over restriction with $p' \circ g = \operatorname{res} \circ p$, and $\delta$, $\delta'$ on $\ker p$, $\ker p'$ with $\delta'(g s) = \operatorname{res}(\delta s)$, one has $\operatorname{res}(\varepsilon_{W,p}^{-1}[\delta]) = \varepsilon_{W',p'}^{-1}[\delta']$. Let $K$ be an ordered affine cover of $P$ (a finite linearly ordered index set $\iota$, affine opens $U_i$ with $\bigsqcup_i U_i = \top$), with ranks $rk_i$, surjections $pr_i : \Gamma(P,U_i)^{rk_i} \to GE(U_i)$ and maps $\delta_i : \ker pr_i \to GK(U_i)$ such that for all $i,j$ and every affine open $W \subseteq U_i \cap U_j$ the restrictions to $W$ of $\varepsilon^{-1}[\delta_i] \in X(U_i)$ and $\varepsilon^{-1}[\delta_j] \in X(U_j)$ coincide. Assume further, chart-wise, for each $i$ and each affine open $U \subseteq U_i$: surjections $prU_{i,U} : \Gamma(P,U)^{rk_i} \to GE(U)$ compatible with $pr_i$ and with restriction; maps $gU_{i,U} : \ker pr_i \to \ker prU_{i,U}$ acting componentwise by restriction of sections, whose image spans $\ker prU_{i,U}$ over $\Gamma(P,U)$; maps $\delta U_{i,U} : \ker prU_{i,U} \to GK(U)$ with $\delta U_{i,U}(gU_{i,U} s) = \operatorname{res}(\delta_i s)$ and compatible with restriction; and additive restriction maps on $M_i(U) := \operatorname{ExtPushout}(prU_{i,U}, \delta U_{i,U})$ — the quotient of $GK(U) \times \Gamma(P,U)^{rk_i}$ by the submodule of pairs $(\delta U_{i,U}(s), -s)$, $s \in \ker prU_{i,U}$ — sending $\mathrm{inl}\,n$ to $\mathrm{inl}$ of the restriction of $n$ and $\mathrm{inr}\,v$ to $\mathrm{inr}$ of the componentwise restriction of $v$. Then, viewing each $M_i(U)$ as an $A$-module through the algebra map $A \to \Gamma(P,U)$ determined by $q$, there exist maps $u_{i,j,W} : M_i(W) \to M_j(W)$, $A$-linear, for all $i, j$ and all affine opens $W \subseteq U_i$ with $W \subseteq U_j$, which are bijective, satisfy $u_{i,j,W}(a \cdot x) = a \cdot u_{i,j,W}(x)$ for $a \in \Gamma(P,W)$, commute with the given restriction maps for affine $W' \subseteq W$, and satisfy $u_{i,j,W} \circ \mathrm{inl} = \mathrm{inl}$ and $\mathrm{proj} \circ u_{i,j,W} = \mathrm{proj}$.
--
--   This is the overlap-comparison step in the construction of a global extension from an $\operatorname{Ext}^1$ class given locally by presentation-wise representatives: the push-out models attached to two charts of the cover are identified over any affine open contained in both, compatibly with restriction and with the inclusion of $GK$ and the projection to $GE$. It is used by [`AlgebraicGeometry.OModulePresheaf.exists_chartModels_extPushout_of_forall_res_symm_mk_eq`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_chartModels_extPushout_of_forall_res_symm_mk_eq), where these identifications are assembled into a coherent system of chart models; separatedness of $q$ is what makes intersections of affine opens affine, so that the comparison can be carried out on $U_i \cap U_j$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_overlapIso_extPushout_of_forall_res_symm_mk_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_LinearMap_ExtPushout

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_overlapIso_extPushout_of_forall_res_symm_mk_eq
    {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsLocallyNoetherian P] [IsSeparated q]
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)

    (X : OModulePresheaf q) (hXc : X.IsCoherent) (hXq : X.IsQuasicoherent)
    (εX : ∀ (W : P.affineOpens) (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] GE.obj W.1), Function.Surjective p →
        (X.obj W.1 ≃ₗ[Γ(P, W.1)]
          ((↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] GK.obj W.1) ⧸
            LinearMap.range (LinearMap.lcomp (Γ(P, W.1)) (GK.obj W.1) (LinearMap.ker p).subtype))))
    (hXf : ∀ (W W' : P.affineOpens) (h : W'.1 ≤ W.1)
        (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] GE.obj W.1) (hp : Function.Surjective p)
        (r' : ℕ) (p' : (Fin r' → Γ(P, W'.1)) →ₗ[Γ(P, W'.1)] GE.obj W'.1) (hp' : Function.Surjective p')
        (g : (Fin r → Γ(P, W.1)) →+ (Fin r' → Γ(P, W'.1)))
        (_hg : ∀ (a : Γ(P, W.1)) (v : Fin r → Γ(P, W.1)), g (a • v) = (P.presheaf.map (homOfLE h).op).hom a • g v)
        (hgp : ∀ v : Fin r → Γ(P, W.1), p' (g v) = GE.res h (p v))
        (δ : ↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] GK.obj W.1) (δ' : ↥(LinearMap.ker p') →ₗ[Γ(P, W'.1)] GK.obj W'.1)
        (hδ : ∀ s : ↥(LinearMap.ker p),
          δ' ⟨g s.1, by rw [LinearMap.mem_ker, hgp, (LinearMap.mem_ker.mp s.2), map_zero]⟩ = GK.res h (δ s)),
        X.res h ((εX W r p hp).symm (Submodule.Quotient.mk δ)) = (εX W' r' p' hp').symm (Submodule.Quotient.mk δ'))

    (K : P.OrderedAffineCover) (rk : K.ι → ℕ)
    (pr : ∀ i : K.ι, (Fin (rk i) → Γ(P, K.U i)) →ₗ[Γ(P, K.U i)] GE.obj (K.U i))
    (hpr : ∀ i : K.ι, Function.Surjective (pr i))
    (δ : ∀ i : K.ι, ↥(LinearMap.ker (pr i)) →ₗ[Γ(P, K.U i)] GK.obj (K.U i))
    (hδ : ∀ (i j : K.ι) (W : P.affineOpens) (hi : W.1 ≤ K.U i) (hj : W.1 ≤ K.U j),
      X.res hi ((εX ⟨K.U i, K.isAffineOpen i⟩ (rk i) (pr i) (hpr i)).symm (Submodule.Quotient.mk (δ i))) =
      X.res hj ((εX ⟨K.U j, K.isAffineOpen j⟩ (rk j) (pr j) (hpr j)).symm (Submodule.Quotient.mk (δ j))))

    (prU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        (Fin (rk i) → Γ(P, U.1.1)) →ₗ[Γ(P, U.1.1)] GE.obj U.1.1)
      (_hprU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (v : Fin (rk i) → Γ(P, K.U i)),
        prU i U (fun m => (P.presheaf.map (homOfLE U.2).op).hom (v m)) = GE.res U.2 (pr i v))
      (_hprUs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (prU i U))
      (_hprUn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (v : Fin (rk i) → Γ(P, U.1.1)),
        prU i U' (fun m => (P.presheaf.map (homOfLE h).op).hom (v m)) = GE.res h (prU i U v))
      (gU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), ↥(LinearMap.ker (pr i)) → ↥(LinearMap.ker (prU i U)))
      (_hgU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (s : ↥(LinearMap.ker (pr i))) (m : Fin (rk i)),
        ((gU i U s : ↥(LinearMap.ker (prU i U))) : Fin (rk i) → Γ(P, U.1.1)) m =
          (P.presheaf.map (homOfLE U.2).op).hom ((s : Fin (rk i) → Γ(P, K.U i)) m))
      (δU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), ↥(LinearMap.ker (prU i U)) →ₗ[Γ(P, U.1.1)] GK.obj U.1.1)
      (_hδU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (s : ↥(LinearMap.ker (pr i))),
        δU i U (gU i U s) = GK.res U.2 (δ i s))
      (_hgUspan : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        Submodule.span Γ(P, U.1.1)
            (Set.range fun s : ↥(LinearMap.ker (pr i)) =>
              ((gU i U s : ↥(LinearMap.ker (prU i U))) : Fin (rk i) → Γ(P, U.1.1))) =
          LinearMap.ker (prU i U))
      (_hδUn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1)
        (s : ↥(LinearMap.ker (prU i U))) (s' : ↥(LinearMap.ker (prU i U'))),
        (∀ m : Fin (rk i), (s' : Fin (rk i) → Γ(P, U'.1.1)) m = (P.presheaf.map (homOfLE h).op).hom ((s : Fin (rk i) → Γ(P, U.1.1)) m)) →
        δU i U' s' = GK.res h (δU i U s))

      (res : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}}, U'.1.1 ≤ U.1.1 →
        LinearMap.ExtPushout (prU i U) (δU i U) → LinearMap.ExtPushout (prU i U') (δU i U'))
      (res_add : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U'.1.1 ≤ U.1.1) (x y : LinearMap.ExtPushout (prU i U) (δU i U)),
        res i h (x + y) = res i h x + res i h y)
      (res_inl : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (n : GK.obj U.1.1),
        res i h (LinearMap.ExtPushout.inl (prU i U) (δU i U) n) = LinearMap.ExtPushout.inl (prU i U') (δU i U') (GK.res h n))
      (res_inr : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (v : Fin (rk i) → Γ(P, U.1.1)),
        res i h (LinearMap.ExtPushout.inr (prU i U) (δU i U) v) =
          LinearMap.ExtPushout.inr (prU i U') (δU i U') (fun m => (P.presheaf.map (homOfLE h).op).hom (v m))) :
    letI : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (LinearMap.ExtPushout (prU i U) (δU i U)) :=
      fun i U => Module.compHom _ (Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1).algebraMap
    ∃ (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), LinearMap.ExtPushout (prU i W) (δU i W) →ₗ[A] LinearMap.ExtPushout (prU j ⟨W.1, hj⟩) (δU j ⟨W.1, hj⟩))
      (hub : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u i j W hj))
      (hus : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : LinearMap.ExtPushout (prU i W) (δU i W)),
          u i j W hj (a • x) = a • u i j W hj x)
      (hun : ∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : LinearMap.ExtPushout (prU i W) (δU i W)),
          u i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u i j W hj x)),
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1),
          u i j W hj (LinearMap.ExtPushout.inl (prU i W) (δU i W) x) = LinearMap.ExtPushout.inl (prU j ⟨W.1, hj⟩) (δU j ⟨W.1, hj⟩) x) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : LinearMap.ExtPushout (prU i W) (δU i W)),
        LinearMap.ExtPushout.proj (prU j ⟨W.1, hj⟩) (δU j ⟨W.1, hj⟩) (u i j W hj x) = LinearMap.ExtPushout.proj (prU i W) (δU i W) x) := by sorry
