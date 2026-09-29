-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isAffineOpen_basicOpen_and_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_mem_vanishingIdeal
-- name    : AlgebraicGeometry.OModulePresheaf.isAffineOpen_basicOpen_and_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_mem_vanishingIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/1048aca8-92f4-508e-8deb-b0987e46a0ad
-- title:
--   Affineness and localisation of the unit over basic opens off T'
-- statement:
--   Fix a Noetherian commutative ring $A$, an ideal $I \subseteq A$, a proper morphism $q : P \to \operatorname{Spec} A$, a closed immersion $i : Z \to P$, a proper morphism $g : V' \to Z$ and an ordered finite affine cover $K'$ of $V'$ (a finite linearly ordered family of affine opens covering $V'$); let $U$ be an open of $Z$ over which $g$ is an isomorphism, in the sense that the second pullback projection of $g$ along $U \hookrightarrow Z$ is an isomorphism, and let $T' \subseteq P$ be closed with $i(z) \in T'$ for every $z \notin U$. The data on $P$ consist of presheaves of modules $F_k$ over $q$, each coherent (finitely generated sections over each affine open) and quasi-coherent (sections over a basic open $D(f)$ are obtained from sections over the ambient affine open up to powers of $f$, and sections killed by restriction are killed by a power of $f$), together with maps $\varphi_k : F_{k+1} \to F_k$ on affine opens which are surjective with kernel $I^{k+1} \cdot F_{k+1}(U_0)$, each $F_k$ being annihilated by the ideal sheaf `i.ker` of $i$. On $V'$ there are presheaves $F'_k$ over $(g \circ i) \circ q$ with maps $\varphi'_k$, and comparison maps $\eta_k : F_k(U_0) \to F'_k(V)$ for affine opens $V \subseteq (g \circ i)^{-1}(U_0)$, semilinear for the structure map $\Gamma(P,U_0) \to \Gamma(V',V)$, compatible with shrinking $V$ and $U_0$ and with $\varphi_k, \varphi'_k$, and inducing isomorphisms $\Gamma(V',V) \otimes_{\Gamma(P,U_0)} F_k(U_0) \cong F'_k(V)$; maps $v_k$ from $F_k$ into the Čech pushforward `cechPushforward` of $F'_k$ along $K'$ are given by the $\eta_k$ on the charts $K'.U_j \cap (g \circ i)^{-1}(U_0)$. Further, $W$ is an affine open of $P$, $R$ a $\Gamma(P,W)$-algebra, $L$ a finite $R$-module which is also a $\Gamma(P,W)$-module compatibly, equipped with $\Gamma(P,W)$-linear maps $\mathrm{pr}_n : L \to F_n(W)$ that are compatible with the $\varphi_n$, jointly injective, surjective, and with $\ker \mathrm{pr}_n$ equal to $J^{n+1} L$ where $J$ is the image of $I$ in $\Gamma(P,W)$; so $L$ realises $\varprojlim F_n(W)$. Finally $sY : Y \to \operatorname{Spec} R$ is proper and $t : Y \to V'$ exhibits $Y$ as the pullback of $g \circ i$ and $\operatorname{Spec} R \to \operatorname{Spec}\Gamma(P,W) \to P$, with $t^{-1}(V)$ affine for every affine open $V \subseteq (g \circ i)^{-1}(W)$; and $G$ is a coherent quasi-coherent presheaf of modules over $sY$ with $R$-linear unit maps $\varepsilon_U : L \to G(U)$ compatible with restriction and inducing isomorphisms $\Gamma(Y,U) \otimes_R L \cong G(U)$ on affine opens. The conclusion is that for every $a$ in the ideal of the vanishing ideal sheaf of $T'$ at $W$, writing $Y_a$ for the basic open of $Y$ cut out by the image of $a$ in $\Gamma(Y,Y)$ (through $\Gamma(P,W) \to R$ and the structure map of $sY$): $Y_a$ is affine; any $x \in L$ with $\varepsilon_{Y_a}(x) = 0$ satisfies $a^k \cdot x = 0$ for some $k$; and every $z \in G(Y_a)$ satisfies $\varepsilon_{Y_a}(x) = a^k \cdot z$ for some $k$ and some $x \in L$, the scalar acting through $\Gamma(P,W) \to R$.
--
--   This is the local affineness-and-localisation step in the proof of Grothendieck's existence theorem for proper morphisms, carried out over the locus where the Chow-lemma modification $g$ is an isomorphism: over the basic open attached to a function vanishing on the exceptional closed set $T'$, the base-changed piece of $Y$ is affine and the unit $\varepsilon$ identifies $G(Y_a)$ with the localisation $L_a$. It is used by [`AlgebraicGeometry.OModulePresheaf.exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_mem_vanishingIdeal_of_isIso_pullback_snd`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_mem_vanishingIdeal_of_isIso_pullback_snd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_isAffineOpen_basicOpen_and_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_mem_vanishingIdeal.lean

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

theorem AlgebraicGeometry.OModulePresheaf.isAffineOpen_basicOpen_and_exists_pow_smul_eq_zero_and_exists_eq_pow_smul_of_mem_vanishingIdeal
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

    {Y : Scheme.{u}} (sY : Y ⟶ Spec (CommRingCat.of R)) [IsProper sY] (t : Y ⟶ V')
    (hY : IsPullback t sY (g ≫ i) (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W.1) R)) ≫ W.2.fromSpec))
    (hta : ∀ V : V'.affineOpens, V.1 ≤ (g ≫ i) ⁻¹ᵁ W.1 → IsAffineOpen (t ⁻¹ᵁ V.1))

    (G : OModulePresheaf sY) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (ε : ∀ U : Y.Opens, L →ₗ[R] G.obj U)
    (hεr : ∀ (U U' : Y.Opens) (h : U ≤ U') (x : L), G.res h (ε U' x) = ε U x)
    (hεβ : ∀ U : Y.affineOpens,
      letI := Scheme.TwoAffineOpenCover.algebraOfHom sY U.1
      ∃ β : Γ(Y, U.1) ⊗[R] L ≃ₗ[Γ(Y, U.1)] G.obj U.1, ∀ x : L, β (1 ⊗ₜ x) = ε U.1 x) :
    ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W,
      IsAffineOpen (Y.basicOpen (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ sY.appLE ⊤ ⊤ le_top).hom (algebraMap Γ(P, W.1) R a))) ∧
      (∀ x : L, ε (Y.basicOpen (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ sY.appLE ⊤ ⊤ le_top).hom (algebraMap Γ(P, W.1) R a))) x = 0 → ∃ k : ℕ, a ^ k • x = 0) ∧
      (∀ z : G.obj (Y.basicOpen (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ sY.appLE ⊤ ⊤ le_top).hom (algebraMap Γ(P, W.1) R a))),
        ∃ (k : ℕ) (x : L), ε (Y.basicOpen (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ sY.appLE ⊤ ⊤ le_top).hom (algebraMap Γ(P, W.1) R a))) x = (algebraMap Γ(P, W.1) R a) ^ k • z) := by sorry
