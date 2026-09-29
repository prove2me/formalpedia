-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top
-- name    : AlgebraicGeometry.OModulePresheaf.exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/d3c72ed1-8c93-53e8-9037-d0a4f34aa8f7
-- title:
--   Base change of an adic datum to a proper frame
-- statement:
--   Let $A$ be a Noetherian commutative ring with ideal $I$, let $q : P \to \operatorname{Spec} A$ be proper, $i : Z \to P$ a closed immersion, $g : V' \to Z$ proper, and $K'$ an ordered affine cover of $V'$ (a finite linearly ordered family of affine opens with supremum $\top$); let $U$ be an open of $Z$ such that the second projection of the pullback of $g$ along $U \hookrightarrow Z$ is an isomorphism, and $T'$ a closed subset of $P$ containing the image under $i$ of every point of $Z$ outside $U$. On $P$ there is given a system $F : \mathbb N \to$ `OModulePresheaf q`, that is, for each $k$ an assignment of an $A$-module $F_k(\mathcal O)$ to each open of $P$ carrying a compatible $\Gamma(P,\mathcal O)$-module structure and semilinear restriction maps, each $F_k$ coherent (finite over $\Gamma(P,\mathcal O)$ on affine opens) and quasicoherent (the usual two conditions on basic opens $D(f)$), together with maps $\varphi_k : F_{k+1} \to F_k$ given on affine opens by $A$-linear, $\Gamma$-semilinear maps compatible with restriction, each surjective on every affine open and with kernel $I^{k+1}\cdot F_{k+1}(\mathcal O)$ there; moreover every element of the ideal of the kernel ideal-sheaf data of $i$ on an affine open annihilates $F_k$ on it. On $V'$ there is given a system $F' : \mathbb N \to$ `OModulePresheaf ((g ≫ i) ≫ q)` with maps $\varphi'_k$ of the same kind, and comparison maps $\eta_k$ assigning to each affine open $U_0$ of $P$ and affine open $V$ of $V'$ with $V \le (g \text{ followed by } i)^{-1}U_0$ an $A$-linear map $F_k(U_0) \to F'_k(V)$, semilinear over $\Gamma(P,U_0) \to \Gamma(V',V)$, compatible with shrinking $V$, with shrinking $U_0$ (via restriction in $F_k$) and with $\varphi_k,\varphi'_k$, and inducing for each such pair a $\Gamma(V',V)$-linear isomorphism $\Gamma(V',V) \otimes_{\Gamma(P,U_0)} F_k(U_0) \cong F'_k(V)$ sending $1 \otimes x$ to $\eta_k(x)$; further, maps $v_k$ from $F_k$ to the Čech pushforward `cechPushforward (g ≫ i) q K' (F' k)`, whose sections over an open $\mathcal O$ are the families $(x_j)_{j \in K'.\iota}$ with $x_j \in F'_k(K'_j \cap p^{-1}\mathcal O)$ agreeing on pairwise intersections, whose $j$-th component on an affine open $U_0$ is $\eta_k$ over the chart $K'_j \cap p^{-1}U_0$. Finally fix an affine open $W$ of $P$, a commutative $\Gamma(P,W)$-algebra $R$, and a module $L$ over both $\Gamma(P,W)$ and $R$ with compatible scalars and finite over $R$, together with $\Gamma(P,W)$-linear maps $\mathrm{pr}_n : L \to F_n(W)$ satisfying $\varphi_n(\mathrm{pr}_{n+1}x) = \mathrm{pr}_n x$, jointly injective, each surjective, and with $\ker \mathrm{pr}_n$ equal to $J^{n+1}L$ where $J$ is the image of $I$ in $\Gamma(P,W)$ under the structure map of $q$. The conclusion asserts the existence of a scheme $Y$, a proper morphism $s_Y : Y \to \operatorname{Spec} R$ and a morphism $t : Y \to V'$ making $(t,s_Y)$ a pullback square over $g$ followed by $i$ and over $\operatorname{Spec}$ of $\Gamma(P,W) \to R$ followed by $W \hookrightarrow P$, such that $t^{-1}V$ is affine for every affine open $V \le (g \text{ followed by } i)^{-1}W$, and of an `OModulePresheaf` $G$ over $s_Y$, $R$-linear maps $\varepsilon_{\mathcal O} : L \to G(\mathcal O)$ for all opens $\mathcal O$ of $Y$, and additive maps $\theta_{n,V} : G(t^{-1}V) \to F'_n(V)$ for such $V$, with: $G$ coherent and quasicoherent; $\varepsilon$ compatible with all restrictions; on each affine open $\mathcal O$ of $Y$ a $\Gamma(Y,\mathcal O)$-linear isomorphism $\Gamma(Y,\mathcal O) \otimes_R L \cong G(\mathcal O)$ with $1 \otimes x \mapsto \varepsilon_{\mathcal O}(x)$; $\theta_{n,V}$ semilinear over $t^\sharp : \Gamma(V',V) \to \Gamma(Y,t^{-1}V)$; $\theta$ compatible with shrinking $V$ and with $\varphi'_n$ in the sense $\varphi'_n(\theta_{n+1,V}y) = \theta_{n,V}y$; $\theta_{n,V}(\varepsilon_{t^{-1}V}x) = \eta_n(W,V)(\mathrm{pr}_n x)$; each $\theta_{n,V}$ surjective; and $\theta_{n,V}y = 0$ if and only if $y$ lies in $J_R^{\,n+1}\cdot G(t^{-1}V)$, where $J_R$ is the image of $I$ in $R$ under $A \to \Gamma(P,W) \to R$.
--
--   This is the local step of Grothendieck's existence theorem in the proper case: over a fixed affine open $W$ of $P$ it base-changes the geometric frame $V' \to P$ along $\operatorname{Spec} R \to W$ and produces on the resulting proper $R$-scheme the module datum attached to the finite $R$-module $L$, together with its levelwise dictionary to the given adic system on $V'$. It is used by [`AlgebraicGeometry.OModulePresheaf.exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_isPullback_isProper_and_exists_forall_surjective_ker_eq_pow_smul_top_of_forall_ker_eq_pow_smul_top
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    {Z : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
    {V' : Scheme.{u}} (g : V' ⟶ Z) [IsProper g] (K' : V'.OrderedAffineCover)
    (U : Z.Opens) (hU : IsIso (CategoryTheory.Limits.pullback.snd g U.ι))
    (T' : Closeds P) (hT' : ∀ z : Z, z ∉ U → i.base z ∈ T')

    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (hFZ : ∀ k, OModulePresheaf.IdealAnnihilates q i.ker (F k))

    (F' : ℕ → OModulePresheaf ((g ≫ i) ≫ q)) (φ' : ∀ k, OModulePresheaf.AffHom (F' (k + 1)) (F' k))
    (η : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1 →
      ((F k).obj U₀.1 →ₗ[A] (F' k).obj V.1))
    (hηs : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (a : Γ(P, U₀.1))
      (x : (F k).obj U₀.1), η k U₀ V h (a • x) = ((g ≫ i).appLE U₀.1 V.1 h).hom a • η k U₀ V h x)
    (hηV : ∀ (k : ℕ) (U₀ : P.affineOpens) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1) (hV : V₁.1 ≤ V₂.1) (x : (F k).obj U₀.1),
      (F' k).res hV (η k U₀ V₂ h₂ x) = η k U₀ V₁ h₁ x)
    (hηU : ∀ (k : ℕ) (U₁ U₂ : P.affineOpens) (V : V'.affineOpens) (h₁ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₁.1)
      (h₂ : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₂.1) (hU₁₂ : U₁.1 ≤ U₂.1) (x : (F k).obj U₂.1),
      η k U₂ V h₂ x = η k U₁ V h₁ ((F k).res hU₁₂ x))
    (hηφ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1)
      (x : (F (k + 1)).obj U₀.1), (φ' k).app V (η (k + 1) U₀ V h x) = η k U₀ V h ((φ k).app U₀ x))
    (hβ : ∀ (k : ℕ) (U₀ : P.affineOpens) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ U₀.1),
      letI := ((g ≫ i).appLE U₀.1 V.1 h).hom.toAlgebra
      ∃ β : Γ(V', V.1) ⊗[Γ(P, U₀.1)] (F k).obj U₀.1 ≃ₗ[Γ(V', V.1)] (F' k).obj V.1,
        ∀ x : (F k).obj U₀.1, β (1 ⊗ₜ x) = η k U₀ V h x)

    (v : ∀ k, OModulePresheaf.AffHom (F k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hvη : ∀ (k : ℕ) (U₀ : P.affineOpens) (x : (F k).obj U₀.1) (j : K'.ι),
      ((v k).app U₀ x).1 j
        = η k U₀ (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' U₀ j)
            (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' U₀.1 j) x)

    (W : P.affineOpens)
    (R : Type u) [CommRing R] [Algebra Γ(P, W.1) R]
    (L : Type u) [AddCommGroup L] [Module Γ(P, W.1) L] [Module R L] [IsScalarTower Γ(P, W.1) R L]
    [Module.Finite R L]
    (pr : ∀ n : ℕ, L →ₗ[Γ(P, W.1)] (F n).obj W.1)
    (hprc : ∀ (n : ℕ) (x : L), (φ n).app W (pr (n + 1) x) = pr n x)
    (hpri : ∀ x : L, (∀ n : ℕ, pr n x = 0) → x = 0)
    (hprs : ∀ n : ℕ, Function.Surjective (pr n))
    (hprk : ∀ n : ℕ, LinearMap.ker (pr n) = (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom) ^ (n + 1) • (⊤ : Submodule Γ(P, W.1) L)) :
    ∃ (Y : Scheme.{u}) (sY : Y ⟶ Spec (CommRingCat.of R)) (_ : IsProper sY) (t : Y ⟶ V'),
      IsPullback t sY (g ≫ i) (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R)) ≫ W.2.fromSpec) ∧
      (∀ V : V'.affineOpens, V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → IsAffineOpen (t ⁻¹ᵁ V.1)) ∧
      ∃ (G : OModulePresheaf sY) (ε : ∀ U : Y.Opens, L →ₗ[R] G.obj U)
        (θ : ∀ (n : ℕ) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → (G.obj (t ⁻¹ᵁ V.1) →+ (F' n).obj V.1)),
        G.IsCoherent ∧ G.IsQuasicoherent ∧
        (∀ (U U' : Y.Opens) (h : U ≤ U') (x : L), G.res h (ε U' x) = ε U x) ∧
        (∀ U : Y.affineOpens,
          letI := Scheme.TwoAffineOpenCover.algebraOfHom sY U.1
          ∃ β : Γ(Y, U.1) ⊗[R] L ≃ₗ[Γ(Y, U.1)] G.obj U.1, ∀ x : L, β (1 ⊗ₜ x) = ε U.1 x) ∧
        (∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (c : Γ(V', V.1))
          (y : G.obj (t ⁻¹ᵁ V.1)), θ n V h ((t.app V.1).hom c • y) = c • θ n V h y) ∧
        (∀ (n : ℕ) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ W.1)
          (hV : V₁.1 ≤ V₂.1) (y : G.obj (t ⁻¹ᵁ V₂.1)),
          (F' n).res hV (θ n V₂ h₂ y) = θ n V₁ h₁ (G.res ((Opens.map t.base).monotone hV) y)) ∧
        (∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
          (φ' n).app V (θ (n + 1) V h y) = θ n V h y) ∧
        (∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (x : L),
          θ n V h (ε (t ⁻¹ᵁ V.1) x) = η n W V h (pr n x)) ∧
        (∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1), Function.Surjective (θ n V h)) ∧
        (∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
          θ n V h y = 0 ↔ y ∈ (I.map ((algebraMap Γ(P, W.1) R).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) ^ (n + 1) • (⊤ : Submodule R (G.obj (t ⁻¹ᵁ V.1)))) := by sorry
