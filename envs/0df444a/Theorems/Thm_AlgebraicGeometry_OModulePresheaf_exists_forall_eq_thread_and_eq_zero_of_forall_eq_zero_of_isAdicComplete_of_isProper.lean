-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/0d464166-8efd-5401-a4b0-0368783be592
-- title:
--   Čech 0-cocycle threads over a complete base: existence, uniqueness, finiteness
-- statement:
--   Throughout, a *module-presheaf datum* over a morphism $\pi : V \to \operatorname{Spec} R$ (the structure `OModulePresheaf`) assigns to each open $O \subseteq V$ an $R$-module together with a $\Gamma(V,O)$-module structure forming a scalar tower over $R$ along $\pi$, plus $R$-linear restriction maps that are semilinear over restriction of rings of sections and are functorial; an `AffHom` between two such data is a family of $R$-linear maps on affine opens, semilinear for the sections, commuting with restriction between affine opens. A module-presheaf datum $F$ is *coherent* when $F(O)$ is a finite $\Gamma(V,O)$-module for every affine open $O$, and *quasi-coherent* when for every affine open $O$ and $f \in \Gamma(V,O)$ every section over the basic open $V_f$ becomes, after multiplication by some power of $f$, the restriction of a section over $O$, and every section over $O$ restricting to $0$ on $V_f$ is killed by some power of $f$.
--
--   **Base geometry.** $A$ is a Noetherian commutative ring, $I \subseteq A$ an ideal, $q : P \to \operatorname{Spec} A$ a proper morphism, $i : Z \to P$ a closed immersion, $g : V' \to Z$ a proper morphism, and $K'$ an ordered affine cover of $V'$: a finite, linearly ordered index type $K'.\iota$ together with affine opens $K'_j \subseteq V'$ whose supremum is $\top$. Furthermore $U$ is an open of $Z$ such that the second projection of the fibre product of $g$ with the inclusion $U \hookrightarrow Z$ is an isomorphism (`hU`), and $T'$ is a closed subset of $P$ such that $i(z) \in T'$ for every point $z$ of $Z$ not lying in $U$ (`hT'`).
--
--   **The $I$-adic system on $P$.** $F : \mathbb{N} \to$ module-presheaf data over $q$, each $F_k$ coherent (`hFc`) and quasi-coherent (`hFq`), with `AffHom`s $\varphi_k : F_{k+1} \to F_k$ such that on every affine open $U_0 \subseteq P$ the map $(\varphi_k)_{U_0}$ is surjective (`hφs`) with kernel $I^{k+1} \cdot F_{k+1}(U_0)$ (`hφk`), and such that each $F_k$ is annihilated by the ideal sheaf of the closed immersion $i$: for every affine open $U_0$ and every $a$ in the ideal $(i.\mathrm{ker})(U_0)$, $a$ kills $F_k(U_0)$ (`hFZ`).
--
--   **The inverse image on $V'$.** $F' : \mathbb{N} \to$ module-presheaf data over the composite of $g$, $i$ and $q$, with `AffHom`s $\varphi'_k : F'_{k+1} \to F'_k$, and comparison maps $\eta_k$ assigning to each affine open $U_0 \subseteq P$ and affine open $V \subseteq V'$ with $V \le (g \ggg i)^{-1}U_0$ an $A$-linear map $F_k(U_0) \to F'_k(V)$. These are required to be: semilinear along the ring map $\Gamma(P,U_0) \to \Gamma(V',V)$ induced by $g$ followed by $i$ (`hηs`); compatible with restriction in $V$ (`hηV`) and with restriction in $U_0$ (`hηU`); compatible with the transition maps, $(\varphi'_k)_V \circ \eta_{k+1} = \eta_k \circ (\varphi_k)_{U_0}$ (`hηφ`); and base-change isomorphisms: for each such pair there is a $\Gamma(V',V)$-linear isomorphism $\Gamma(V',V) \otimes_{\Gamma(P,U_0)} F_k(U_0) \cong F'_k(V)$ carrying $1 \otimes x$ to $\eta_k(x)$ (`hβ`).
--
--   **Čech comparison.** For an open $O \subseteq Z$ (or of $P$ through the composite) write $C_j(O) := K'_j \cap (g \ggg i)^{-1}O$ for the $j$-th chart; the Čech pushforward `cechPushforward` of a datum $F'_n$ sends $O$ to the module of $0$-cocycles, i.e. families $(x_j)_j$ with $x_j \in F'_n(C_j(O))$ agreeing after restriction to $C_j(O) \cap C_{j'}(O)$ for all $j,j'$. The data include `AffHom`s $v_k$ from $F_k$ to the Čech pushforward of $F'_k$, whose $j$-th component at an affine open $U_0$ is $\eta_k$ at the affine chart $C_j(U_0)$ (`hvη`).
--
--   **The completed chart.** $W$ is an affine open of $P$; $R$ is a commutative $\Gamma(P,W)$-algebra; $L$ is an abelian group carrying a $\Gamma(P,W)$-module and an $R$-module structure forming a scalar tower, finite over $R$; and $\mathrm{pr}_n : L \to F_n(W)$ are $\Gamma(P,W)$-linear maps with $(\varphi_n)_W \circ \mathrm{pr}_{n+1} = \mathrm{pr}_n$ (`hprc`), jointly injective (`hpri`), each surjective (`hprs`), and with $\ker \mathrm{pr}_n = I_W^{\,n+1} L$, where $I_W$ is the image of $I$ in $\Gamma(P,W)$ under the structure map induced by $q$ (`hprk`). Moreover $R$ is Noetherian and complete for the adic topology of the image of $I$ in $R$ (`hRc`).
--
--   **The base-changed space and module.** $s_Y : Y \to \operatorname{Spec} R$ is proper and $t : Y \to V'$ is a morphism such that the square formed by $t$, $s_Y$, $g$ followed by $i$, and $\operatorname{Spec}$ of $\Gamma(P,W) \to R$ followed by the canonical morphism $\operatorname{Spec} \Gamma(P,W) \to P$ is a pullback (`hY`), and $t^{-1}V$ is affine for every affine open $V \subseteq V'$ with $V \le (g \ggg i)^{-1}W$ (`hta`). $G$ is a coherent (`hGc`) and quasi-coherent (`hGq`) module-presheaf datum over $s_Y$, equipped with $R$-linear maps $\varepsilon_O : L \to G(O)$ for all opens $O$ of $Y$, compatible with restriction (`hεr`), and such that on every affine open $O$ there is a $\Gamma(Y,O)$-linear isomorphism $\Gamma(Y,O) \otimes_R L \cong G(O)$ carrying $1 \otimes x$ to $\varepsilon_O(x)$ (`hεβ`).
--
--   **The reduction maps $\theta$.** For each $n$ and each affine open $V \subseteq V'$ with $V \le (g \ggg i)^{-1}W$, $\theta_{n,V} : G(t^{-1}V) \to F'_n(V)$ is additive, semilinear along $t$ in the sense $\theta_{n,V}(t^\sharp(c) \cdot y) = c \cdot \theta_{n,V}(y)$ for $c \in \Gamma(V',V)$ (`hθs`), compatible with restriction in $V$ (`hθr`), compatible with the transition maps, $(\varphi'_n)_V \circ \theta_{n+1,V} = \theta_{n,V}$ (`hθφ`), compatible with the units, $\theta_{n,V}(\varepsilon_{t^{-1}V}(x)) = \eta_n(\mathrm{pr}_n x)$ (`hθε`), surjective (`hθo`), and with $\theta_{n,V}(y) = 0$ if and only if $y$ lies in $I_R^{\,n+1} \cdot G(t^{-1}V)$, $I_R$ the image of $I$ in $R$ (`hθk`).
--
--   Write $C_j := K'_j \cap (g \ggg i)^{-1}W$ for the charts over $W$ (affine opens, by `affineChart`). The conclusion is the conjunction of three assertions about families indexed by $j \in K'.\iota$ of sections of $G$ over the $t^{-1}C_j$; such a family $c = (c_j)_j$ is called *compatible* when for all $j,j'$ the restrictions of $c_j$ and of $c_{j'}$ to $t^{-1}(C_j \cap C_{j'})$ agree.
--
--   1.
--
--   (Existence.) For every family $\ell$ with $\ell_n$ a Čech $0$-cocycle of $F'_n$ over $W$, such that the Čech pushforward of $\varphi'_n$ at $W$ carries $\ell_{n+1}$ to $\ell_n$ for all $n$, there exists a compatible family $c = (c_j)_j$, $c_j \in G(t^{-1}C_j)$, with $\theta_{n,C_j}(c_j) = (\ell_n)_j$ for all $n$ and all $j$.
--
--   2.
--
--   (Uniqueness.) Every compatible family $c$ with $\theta_{n,C_j}(c_j) = 0$ for all $n$ and $j$ is zero.
--
--   3.
--
--   (Finiteness.) There is a finite subset $s$ of $\prod_j G(t^{-1}C_j)$, each member of which is compatible, such that every compatible family lies in the $R$-submodule spanned by $s$.
--
--   This is the degree-zero formal-functions step in the proof of Grothendieck's existence theorem, in the form used on a single affine chart $W$ of the proper base: over the $I$-adically complete Noetherian ring $R$ it identifies threads of Čech $0$-cocycles of the system $(F'_n, \varphi'_n)$ over $W$ with compatible families of sections of $G$ on the base-changed charts, and adds uniqueness and finite generation of the module of compatible families. It is invoked by [`AlgebraicGeometry.OModulePresheaf.exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper.lean

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

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_eq_thread_and_eq_zero_of_forall_eq_zero_of_isAdicComplete_of_isProper
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
    (hprk : ∀ n : ℕ, LinearMap.ker (pr n) = (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom) ^ (n + 1) • (⊤ : Submodule Γ(P, W.1) L))
    [IsNoetherianRing R] (hRc : IsAdicComplete (I.map ((algebraMap Γ(P, W.1) R).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) R)

    {Y : Scheme.{u}} (sY : Y ⟶ Spec (CommRingCat.of R)) [IsProper sY] (t : Y ⟶ V')
    (hY : IsPullback t sY (g ≫ i) (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R)) ≫ W.2.fromSpec))
    (hta : ∀ V : V'.affineOpens, V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → IsAffineOpen (t ⁻¹ᵁ V.1))

    (G : OModulePresheaf sY) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (ε : ∀ U : Y.Opens, L →ₗ[R] G.obj U)
    (hεr : ∀ (U U' : Y.Opens) (h : U ≤ U') (x : L), G.res h (ε U' x) = ε U x)
    (hεβ : ∀ U : Y.affineOpens,
      letI := Scheme.TwoAffineOpenCover.algebraOfHom sY U.1
      ∃ β : Γ(Y, U.1) ⊗[R] L ≃ₗ[Γ(Y, U.1)] G.obj U.1, ∀ x : L, β (1 ⊗ₜ x) = ε U.1 x)

    (θ : ∀ (n : ℕ) (V : V'.affineOpens), V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → (G.obj (t ⁻¹ᵁ V.1) →+ (F' n).obj V.1))
    (hθs : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (c : Γ(V', V.1))
      (y : G.obj (t ⁻¹ᵁ V.1)), θ n V h ((t.app V.1).hom c • y) = c • θ n V h y)
    (hθr : ∀ (n : ℕ) (V₁ V₂ : V'.affineOpens) (h₁ : V₁.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (h₂ : V₂.1 ≤ (g ≫ i) ⁻¹ᵁ W.1)
      (hV : V₁.1 ≤ V₂.1) (y : G.obj (t ⁻¹ᵁ V₂.1)),
      (F' n).res hV (θ n V₂ h₂ y) = θ n V₁ h₁ (G.res ((Opens.map t.base).monotone hV) y))
    (hθφ : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
      (φ' n).app V (θ (n + 1) V h y) = θ n V h y)
    (hθε : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (x : L),
      θ n V h (ε (t ⁻¹ᵁ V.1) x) = η n W V h (pr n x))
    (hθo : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1), Function.Surjective (θ n V h))
    (hθk : ∀ (n : ℕ) (V : V'.affineOpens) (h : V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1) (y : G.obj (t ⁻¹ᵁ V.1)),
      θ n V h y = 0 ↔ y ∈ (I.map ((algebraMap Γ(P, W.1) R).comp ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W.1 le_top).hom)) ^ (n + 1) • (⊤ : Submodule R (G.obj (t ⁻¹ᵁ V.1)))) :
    (∀ (ℓ : ∀ n, (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' n)).obj W.1),
        (∀ n, ((φ' n).cechPushforward (g ≫ i) q K').app W (ℓ (n + 1)) = ℓ n) →
        ∃ c : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)),
          (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j')) ∧
          ∀ (n : ℕ) (j : K'.ι),
            θ n (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' W j)
              (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' W.1 j) (c j) = (ℓ n).1 j) ∧
    (∀ c : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)),
        (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j')) →
        (∀ (n : ℕ) (j : K'.ι),
            θ n (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' W j)
              (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' W.1 j) (c j) = 0) →
        c = 0) ∧
    (∃ s : Finset (∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j))),
        (∀ c ∈ s, (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j'))) ∧
        ∀ c : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)),
          (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j')) → c ∈ Submodule.span R (s : Set (∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j))))) := by sorry
