-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_chartModels_extPushout_of_forall_res_symm_mk_eq
-- name    : AlgebraicGeometry.OModulePresheaf.exists_chartModels_extPushout_of_forall_res_symm_mk_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/16d63845-fbc9-51c0-b59d-90ca9dc92f46
-- title:
--   Chart-wise push-out models for agreeing local Ext classes
-- statement:
--   Throughout, $A$ is a commutative ring, $P$ a locally Noetherian scheme, and $q : P \to \operatorname{Spec} A$ a separated morphism. An `OModulePresheaf q` is a family of module data: for each open $U \subseteq P$ an abelian group $F(U)$ carrying both an $A$-module and a $\Gamma(P,U)$-module structure, compatible through the ring map $A \to \Gamma(P,U)$ attached to $q$ (a scalar tower), together with $A$-linear restrictions $F(U') \to F(U)$ for $U \le U'$ which are semilinear over the restriction of scalars ($\mathrm{res}_h(a \cdot x) = a|_U \cdot \mathrm{res}_h(x)$) and satisfy the presheaf identities $\mathrm{res}_{\le} = \mathrm{id}$ and $\mathrm{res}_{h \circ h'} = \mathrm{res}_h \circ \mathrm{res}_{h'}$. Such an $F$ is *coherent* when $F(U)$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and *quasi-coherent* when for every affine open $U$ and every $g \in \Gamma(P,U)$: each element of $F(D(g))$ becomes the restriction of an element of $F(U)$ after multiplication by the restriction of some power $g^n$, and each element of $F(U)$ restricting to $0$ on $D(g)$ is annihilated by some power of $g$.
--
--   The data assumed are: three such families $G_E$, $G_K$ and $X$, each assumed coherent and quasi-coherent (hypotheses `hGEc`, `hGEq`, `hGKc`, `hGKq`, `hXc`, `hXq`); a presentation-wise identification `εX` which assigns to every affine open $W$, every $r \in \mathbb{N}$ and every surjective $\Gamma(P,W)$-linear $p : \Gamma(P,W)^r \to G_E(W)$ a $\Gamma(P,W)$-linear isomorphism
--   $$X(W) \;\cong\; \operatorname{Hom}_{\Gamma(P,W)}(\ker p,\, G_K(W)) \big/ \operatorname{im}\big(\operatorname{Hom}_{\Gamma(P,W)}(\Gamma(P,W)^r, G_K(W)) \to \operatorname{Hom}_{\Gamma(P,W)}(\ker p, G_K(W))\big),$$
--   the quotient being by the range of precomposition with the inclusion $\ker p \hookrightarrow \Gamma(P,W)^r$; and the functoriality hypothesis `hXf`, which requires, for affine opens $W' \le W$, surjections $p : \Gamma(P,W)^r \to G_E(W)$ and $p' : \Gamma(P,W')^{r'} \to G_E(W')$, an additive map $g : \Gamma(P,W)^r \to \Gamma(P,W')^{r'}$ that is semilinear over the restriction of scalars and satisfies $p' \circ g = \mathrm{res} \circ p$, and maps $\delta : \ker p \to G_K(W)$, $\delta' : \ker p' \to G_K(W')$ with $\delta'(g s) = \mathrm{res}(\delta s)$ for all $s \in \ker p$, that the restriction to $W'$ of $\varepsilon_{W,p}^{-1}[\delta]$ equal $\varepsilon_{W',p'}^{-1}[\delta']$ in $X(W')$.
--
--   Finally, $K$ is an ordered affine cover of $P$: a finite linearly ordered index type $\iota$ together with affine opens $U_i$ whose supremum is $\top$. For each $i$ there are given a rank $rk\,i$, a surjective $\Gamma(P,U_i)$-linear map $pr_i : \Gamma(P,U_i)^{rk\,i} \to G_E(U_i)$ (hypothesis `hpr`) and a $\Gamma(P,U_i)$-linear $\delta_i : \ker(pr_i) \to G_K(U_i)$, subject to the agreement hypothesis `hδ`: for all $i, j$ and every affine open $W$ with $W \le U_i$ and $W \le U_j$, the restrictions to $W$ of $\varepsilon_{U_i, pr_i}^{-1}[\delta_i]$ and of $\varepsilon_{U_j, pr_j}^{-1}[\delta_j]$ coincide in $X(W)$.
--
--   The assertion is the existence of the following data. First, chart-wise base-changed presentations: for each $i$ and each affine open $U \le U_i$ a $\Gamma(P,U)$-linear $prU_{i,U} : \Gamma(P,U)^{rk\,i} \to G_E(U)$ satisfying $prU_{i,U}(v|_U) = \mathrm{res}(pr_i v)$ coordinatewise (`_hprU`) and surjective (`_hprUs`); a map $gU_{i,U} : \ker(pr_i) \to \ker(prU_{i,U})$ given coordinatewise by restriction of sections (`_hgU`); a $\Gamma(P,U)$-linear $\delta U_{i,U} : \ker(prU_{i,U}) \to G_K(U)$ with $\delta U_{i,U}(gU_{i,U}(s)) = \mathrm{res}(\delta_i s)$ (`_hδU`); and the spanning condition `_hgUspan`, that the $\Gamma(P,U)$-submodule of $\Gamma(P,U)^{rk\,i}$ spanned by the image of $gU_{i,U}$ is exactly $\ker(prU_{i,U})$.
--
--   Write $M_i(U) := \operatorname{ExtPushout}(prU_{i,U}, \delta U_{i,U})$, the quotient of $G_K(U) \times \Gamma(P,U)^{rk\,i}$ by the range of $s \mapsto (\delta U_{i,U}(s), -s)$ on $\ker(prU_{i,U})$, with its $A$-module structure obtained from its $\Gamma(P,U)$-module structure along the ring map $A \to \Gamma(P,U)$ coming from $q$. Then there further exist: witnesses that $A$, $\Gamma(P,U)$ and $M_i(U)$ form a scalar tower; $A$-linear restriction maps $\mathrm{res}_i^h : M_i(U) \to M_i(U')$ for affine opens $U' \le U$ inside $U_i$, satisfying semilinearity over restriction of scalars (`res_smul`), $\mathrm{res}_i^{\le} = \mathrm{id}$ (`res_refl`) and transitivity (`res_comp`); the quasi-coherence clause `hqc`, stating for $U$ and $U_g$ affine opens inside $U_i$ with $U_g = D(g)$ for $g \in \Gamma(P,U)$ that every element of $M_i(U_g)$ equals $g^n|_{U_g} \cdot (\text{restriction of some element of } M_i(U))$ for some $n$, and that every element of $M_i(U)$ restricting to $0$ on $U_g$ is killed by some power of $g$; finiteness of $M_i(U)$ as a $\Gamma(P,U)$-module (`hfg`); $A$-linear maps $\vartheta_{i,U} : G_K(U) \to M_i(U)$ and $\theta_{E,i,U} : M_i(U) \to G_E(U)$ which commute with multiplication by scalars from $\Gamma(P,U)$ (`hϑs`, `hθEs`) and with restrictions, in the sense $\vartheta_{i,U'}(\mathrm{res}\,x) = \mathrm{res}_i^h(\vartheta_{i,U}x)$ and $\theta_{E,i,U'}(\mathrm{res}_i^h x) = \mathrm{res}(\theta_{E,i,U}x)$ (`hϑn`, `hθEn`), with $\operatorname{range}(\vartheta_{i,U}) = \ker(\theta_{E,i,U})$ (`hexact`), $\theta_{E,i,U}$ surjective (`hsurj`) and $\vartheta_{i,U}$ injective (`hϑi`); and overlap comparison maps $u_{i,j,W} : M_i(W) \to M_j(W)$, for $W$ an affine open contained in both $U_i$ and $U_j$, which are $A$-linear and bijective (`hub`), commute with multiplication by scalars from $\Gamma(P,W)$ (`hus`), are compatible with the restrictions of both charts (`hun`), and satisfy $u_{i,j,W} \circ \vartheta_{i,W} = \vartheta_{j,W}$ (`huϑ`) and $\theta_{E,j,W} \circ u_{i,j,W} = \theta_{E,i,W}$ (`huθE`).
--
--   For this data the conclusion is the conjunction of four statements: $\vartheta_{i,U}$ is the canonical map [`LinearMap.ExtPushout.inl`](def/LinearMap_ExtPushout.html#L40) of the push-out; $\theta_{E,i,U}$ is the canonical projection [`LinearMap.ExtPushout.proj`](def/LinearMap_ExtPushout.html#L55), induced by $prU_{i,U}$ on the second factor; for $U' \le U$ inside $U_i$ and $n \in G_K(U)$, $\mathrm{res}_i^h(\mathrm{inl}\,n) = \mathrm{inl}(\mathrm{res}_h\,n)$; and for $v \in \Gamma(P,U)^{rk\,i}$, $\mathrm{res}_i^h(\mathrm{inr}\,v) = \mathrm{inr}(v|_{U'})$, the restriction being taken coordinatewise.
--
--   This is the chart-local step in constructing a global extension of coherent module data out of a family of local $\mathrm{Ext}^1$ classes that agree on overlaps: each chart of an ordered affine cover is equipped with the push-out extension of its presentation along the given $\delta_i$, together with functorial quasi-coherent restrictions, the exact sequence $0 \to G_K \to M_i \to G_E \to 0$, and isomorphisms between the models of two charts over a common affine open. It is used by [`AlgebraicGeometry.OModulePresheaf.exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete), where these chart models are assembled under properness and adic completeness hypotheses.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_chartModels_extPushout_of_forall_res_symm_mk_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_LinearMap_ExtPushout

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_chartModels_extPushout_of_forall_res_symm_mk_eq
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
      X.res hj ((εX ⟨K.U j, K.isAffineOpen j⟩ (rk j) (pr j) (hpr j)).symm (Submodule.Quotient.mk (δ j)))) :
    ∃ (prU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        (Fin (rk i) → Γ(P, U.1.1)) →ₗ[Γ(P, U.1.1)] GE.obj U.1.1)
      (_hprU : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (v : Fin (rk i) → Γ(P, K.U i)),
        prU i U (fun m => (P.presheaf.map (homOfLE U.2).op).hom (v m)) = GE.res U.2 (pr i v))
      (_hprUs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (prU i U))
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
          LinearMap.ker (prU i U)),
    letI : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (LinearMap.ExtPushout (prU i U) (δU i U)) :=
      fun i U => Module.compHom _ (Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1).algebraMap
    ∃ (_ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
          letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1
          IsScalarTower A Γ(P, U.1.1) (LinearMap.ExtPushout (prU i U) (δU i U)))
      (res : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}}, U'.1.1 ≤ U.1.1 → (LinearMap.ExtPushout (prU i U) (δU i U) →ₗ[A] LinearMap.ExtPushout (prU i U') (δU i U')))
      (res_smul : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U'.1.1 ≤ U.1.1) (a : Γ(P, U.1.1)) (x : LinearMap.ExtPushout (prU i U) (δU i U)),
          res i h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res i h x)
      (res_refl : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (x : LinearMap.ExtPushout (prU i U) (δU i U)), res i (le_refl U.1.1) x = x)
      (res_comp : ∀ (i : K.ι) {U U' U'' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U''.1.1 ≤ U'.1.1) (h' : U'.1.1 ≤ U.1.1)
          (x : LinearMap.ExtPushout (prU i U) (δU i U)), res i (h.trans h') x = res i h (res i h' x))
      (hqc : ∀ (i : K.ι) (U Ug : {U : P.affineOpens // U.1 ≤ K.U i}) (g : Γ(P, U.1.1)) (hUg : Ug.1.1 = P.basicOpen g),
          (∀ y : LinearMap.ExtPushout (prU i Ug) (δU i Ug), ∃ (n : ℕ) (x : LinearMap.ExtPushout (prU i U) (δU i U)),
              res i (hUg.trans_le (P.basicOpen_le g)) x =
                (P.presheaf.map (homOfLE (hUg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
          (∀ x : LinearMap.ExtPushout (prU i U) (δU i U), res i (hUg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
      (hfg : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module.Finite (Γ(P, U.1.1) : Type u) (LinearMap.ExtPushout (prU i U) (δU i U)))
      (ϑ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), GK.obj U.1.1 →ₗ[A] LinearMap.ExtPushout (prU i U) (δU i U))
      (θE : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), LinearMap.ExtPushout (prU i U) (δU i U) →ₗ[A] GE.obj U.1.1)
            (hϑs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ i U (a • x) = a • ϑ i U x)
      (hθEs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : LinearMap.ExtPushout (prU i U) (δU i U)), θE i U (a • x) = a • θE i U x)
            (hϑn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : GK.obj U.1.1),
          ϑ i U' (GK.res h x) = res i h (ϑ i U x))
      (hθEn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : LinearMap.ExtPushout (prU i U) (δU i U)),
          θE i U' (res i h x) = GE.res h (θE i U x))
            (hexact : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), LinearMap.range (ϑ i U) = LinearMap.ker (θE i U))
      (hsurj : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (θE i U))
      (hϑi : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Injective (ϑ i U))
      (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), LinearMap.ExtPushout (prU i W) (δU i W) →ₗ[A] LinearMap.ExtPushout (prU j ⟨W.1, hj⟩) (δU j ⟨W.1, hj⟩))
      (hub : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u i j W hj))
      (hus : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : LinearMap.ExtPushout (prU i W) (δU i W)),
          u i j W hj (a • x) = a • u i j W hj x)
      (hun : ∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : LinearMap.ExtPushout (prU i W) (δU i W)),
          u i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u i j W hj x))
      (huϑ : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1),
          u i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x)
      (huθE : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : LinearMap.ExtPushout (prU i W) (δU i W)),
        θE j ⟨W.1, hj⟩ (u i j W hj x) = θE i W x),

      (∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (x : GK.obj U.1.1),
        ϑ i U x = LinearMap.ExtPushout.inl (prU i U) (δU i U) x) ∧
      (∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (x : LinearMap.ExtPushout (prU i U) (δU i U)),
        θE i U x = LinearMap.ExtPushout.proj (prU i U) (δU i U) x) ∧
      (∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (n : GK.obj U.1.1),
        res i h (LinearMap.ExtPushout.inl (prU i U) (δU i U) n) = LinearMap.ExtPushout.inl (prU i U') (δU i U') (GK.res h n)) ∧
      (∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (v : Fin (rk i) → Γ(P, U.1.1)),
        res i h (LinearMap.ExtPushout.inr (prU i U) (δU i U) v) =
          LinearMap.ExtPushout.inr (prU i U') (δU i U') (fun m => (P.presheaf.map (homOfLE h).op).hom (v m))) := by sorry
