-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_and_exists_eq_smul_of_le_of_flat_of_bijective
-- name    : AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_and_exists_eq_smul_of_le_of_flat_of_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/726716a1-3bdf-56f0-9546-9ebf65d3a13b
-- title:
--   Flat base change of Čech torsion and solvability from W₀ to W
-- statement:
--   Throughout, $A$ is a Noetherian commutative ring and $I \subseteq A$ an ideal.
--
--   **Ambient proper setting.** $q : P \to \operatorname{Spec} A$ is a proper morphism of schemes, $i : Z \to P$ a closed immersion, $g : V' \to Z$ a proper morphism, and $K'$ an ordered affine cover of $V'$, i.e. a finite linearly ordered index type $K'.\iota$ together with opens $K'.U_j \subseteq V'$, each affine, whose supremum is $\top$. Further data: an open $U \subseteq Z$ such that the second projection of the pullback of $g$ along the inclusion $U \hookrightarrow Z$ is an isomorphism (`hU`), and a closed subset $T' \subseteq P$ such that $i$ carries every point of $Z$ outside $U$ into $T'$ (`hT'`).
--
--   **The $I$-adic system on $P$.** $F : \mathbb{N} \to$ `OModulePresheaf q` assigns to each $k$ a presheaf of modules over $q$: a family of $A$-modules $(F k)(U_0)$ indexed by the opens $U_0$ of $P$, each also a $\Gamma(P,U_0)$-module compatibly with the $A$-algebra structure coming from $q$, with $A$-linear restriction maps that are semilinear for the restriction of sections, reflexive and transitive. Each $F k$ is coherent (`hFc`: $(F k)(U_0)$ is a finite $\Gamma(P,U_0)$-module for every affine open $U_0$) and quasi-coherent (`hFq`: for every affine open $U_0$ and $f \in \Gamma(P,U_0)$, every section over the basic open $D(f)$ becomes, after multiplication by some power of $f$, the restriction of a section over $U_0$, and every section over $U_0$ restricting to $0$ on $D(f)$ is annihilated by some power of $f$). The maps $\varphi_k$ are `AffHom`s $F(k+1) \to F k$, i.e. families of $A$-linear maps on affine opens commuting with multiplication by sections and with restriction between affine opens. They satisfy: `hφs`, each $(\varphi_k)_{U_0}$ is surjective; `hφk`, $\ker (\varphi_k)_{U_0} = I^{k+1} \cdot (F(k+1))(U_0)$ as $A$-submodules; and `hFZ`, `IdealAnnihilates q i.ker (F k)`, i.e. for every affine open $U_0$ of $P$ every element of the ideal of the kernel ideal sheaf data of $i$ over $U_0$ annihilates $(F k)(U_0)$.
--
--   **The inverse image on $V'$.** $F' : \mathbb{N} \to$ `OModulePresheaf ((g ≫ i) ≫ q)` with `AffHom`s $\varphi'_k : F'(k+1) \to F' k$, together with comparison maps $\eta$: for each $k$, each affine open $U_0 \subseteq P$ and each affine open $V \subseteq V'$ with $V \le (g \text{ followed by } i)^{-1}U_0$, an $A$-linear map $\eta_k(U_0,V) : (F k)(U_0) \to (F' k)(V)$. These are required to be semilinear for the ring map $\Gamma(P,U_0) \to \Gamma(V',V)$ induced by $g$ followed by $i$ (`hηs`), compatible with shrinking $V$ (`hηV`), compatible with shrinking $U_0$ in the sense that $\eta_k(U_2,V) = \eta_k(U_1,V) \circ (F k).\mathrm{res}$ for $U_1 \le U_2$ (`hηU`), and compatible with the transition maps, $(\varphi'_k)_V \circ \eta_{k+1}(U_0,V) = \eta_k(U_0,V) \circ (\varphi_k)_{U_0}$ (`hηφ`); and `hβ` asserts that each $\eta_k(U_0,V)$ exhibits $(F' k)(V)$ as a base change: there is a $\Gamma(V',V)$-linear equivalence $\beta : \Gamma(V',V) \otimes_{\Gamma(P,U_0)} (F k)(U_0) \xrightarrow{\sim} (F' k)(V)$ with $\beta(1 \otimes x) = \eta_k(U_0,V)(x)$, the algebra structure being the one given by $(g \text{ followed by } i).\mathrm{appLE}$.
--
--   **The Čech comparison.** For each $k$, $v_k$ is an `AffHom` from $F k$ to `OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)`, whose value on an open $U_0$ is the module of $0$-cocycles for $F' k$ on the charts `cechPushforward.chart (g ≫ i) K' U₀ j` $= K'.U_j \sqcap (g \text{ followed by } i)^{-1}U_0$; `hvη` identifies the $j$-th component of $(v_k)_{U_0}(x)$ with $\eta_k(U_0, \text{chart}_j)(x)$.
--
--   **The local frame over $W_0$.** $W_0$ is an affine open of $P$, $R_0$ a commutative $\Gamma(P,W_0)$-algebra, and $L_0$ an abelian group carrying compatible $\Gamma(P,W_0)$- and $R_0$-module structures (scalar tower) with $L_0$ finite over $R_0$, together with $\Gamma(P,W_0)$-linear maps $\mathrm{pr}^0_n : L_0 \to (F n)(W_0)$ such that $(\varphi_n)_{W_0} \circ \mathrm{pr}^0_{n+1} = \mathrm{pr}^0_n$ (`hprc₀`), the family $(\mathrm{pr}^0_n)_n$ is jointly injective (`hpri₀`), each $\mathrm{pr}^0_n$ is surjective (`hprs₀`), and $\ker \mathrm{pr}^0_n = J_0^{\,n+1} L_0$ where $J_0$ is the image of $I$ in $\Gamma(P,W_0)$ under the structure map of $q$ (`hprk₀`). Geometrically: $s_{Y_0} : Y_0 \to \operatorname{Spec} R_0$ is proper, $t_0 : Y_0 \to V'$, and `hY₀` says that $(t_0, s_{Y_0})$ is a pullback square over $g$ followed by $i$ and $\operatorname{Spec}$ of $\Gamma(P,W_0) \to R_0$ followed by $W_0.\mathrm{fromSpec}$; `hta₀` says $t_0^{-1}V$ is affine for every affine open $V \le (g \text{ followed by } i)^{-1}W_0$. Finally $G_0$ is a coherent quasi-coherent presheaf of modules over $s_{Y_0}$ (in the senses unfolded above) with $R_0$-linear unit maps $\varepsilon_0(U) : L_0 \to G_0(U)$ for all opens $U \subseteq Y_0$, compatible with restriction (`hεr₀`), and such that on each affine open $U$ there is a $\Gamma(Y_0,U)$-linear equivalence $\Gamma(Y_0,U) \otimes_{R_0} L_0 \xrightarrow{\sim} G_0(U)$ sending $1 \otimes x$ to $\varepsilon_0(U)(x)$ (`hεβ₀`).
--
--   **The local frame over $W$.** The same package is assumed verbatim for an affine open $W \subseteq P$: a $\Gamma(P,W)$-algebra $R$, a module $L$ finite over $R$ with compatible $\Gamma(P,W)$-structure, maps $\mathrm{pr}_n : L \to (F n)(W)$ with the four properties `hprc`, `hpri`, `hprs`, `hprk` (kernel equal to the $(n+1)$-st power of the image of $I$ in $\Gamma(P,W)$ times $L$), a proper $s_Y : Y \to \operatorname{Spec} R$ with $t : Y \to V'$ and the pullback property `hY`, affineness of the preimages `hta`, and a coherent quasi-coherent $G$ over $s_Y$ with unit maps $\varepsilon$ satisfying `hεr` and `hεβ`.
--
--   **The flat comparison.** $W \le W_0$ (`hW`); $R$ is an $R_0$-algebra, flat over $R_0$; `hR` requires that for every $b \in \Gamma(P,W_0)$ the image of $b$ in $R$ via $\Gamma(P,W_0) \to R_0 \to R$ agrees with the image of its restriction to $W$ via $\Gamma(P,W) \to R$; and $e : R \otimes_{R_0} L_0 \to L$ is an $R$-linear map which is bijective (`heb`) and satisfies $\mathrm{pr}_n(e(1 \otimes x_0)) = (F n).\mathrm{res}_{W \le W_0}(\mathrm{pr}^0_n(x_0))$ for all $n$ and $x_0$ (`he`).
--
--   **The hypotheses over $W_0$.** With $N \in \mathbb{N}$ fixed and $\mathcal{J}$ denoting the vanishing ideal sheaf data of the closed set $T'$: `hk₀` states that if $x \in L_0$ has $\varepsilon_0\big(t_0^{-1}(K'.U_j \sqcap (g \text{ followed by } i)^{-1}W_0)\big)(x) = 0$ for every $j \in K'.\iota$, then $a \cdot x = 0$ for every $a \in \mathcal{J}(W_0)^N$; and `hc₀` states that for every family $c = (c_j)_{j \in K'.\iota}$ with $c_j \in G_0\big(t_0^{-1}(K'.U_j \sqcap (g \text{ followed by } i)^{-1}W_0)\big)$ whose members agree after restriction to the preimages under $t_0$ of the pairwise intersections of those charts, and for every $a \in \mathcal{J}(W_0)^N$, there exists $x \in L_0$ with $\varepsilon_0\big(t_0^{-1}(\text{chart}_j)\big)(x) = (\text{image of } a \text{ in } R_0) \cdot c_j$ for all $j$.
--
--   **Conclusion.** The conjunction of the two corresponding statements over $W$:
--
--   First, for every $x \in L$: if $\varepsilon\big(t^{-1}(K'.U_j \sqcap (g \text{ followed by } i)^{-1}W)\big)(x) = 0$ for every $j \in K'.\iota$, then $a \cdot x = 0$ for every $a \in \mathcal{J}(W)^N$, the action being that of $\Gamma(P,W)$ on $L$.
--
--   Second, for every family $c = (c_j)_{j \in K'.\iota}$ with $c_j \in G\big(t^{-1}(K'.U_j \sqcap (g \text{ followed by } i)^{-1}W)\big)$ such that for all $j, j'$ the restrictions of $c_j$ and $c_{j'}$ to the $t$-preimage of $\text{chart}_j \sqcap \text{chart}_{j'}$ coincide, and for every $a \in \mathcal{J}(W)^N$, there exists $x \in L$ with $\varepsilon\big(t^{-1}(\text{chart}_j)\big)(x) = (\text{image of } a \text{ in } R \text{ under } \Gamma(P,W) \to R) \cdot c_j$ for every $j \in K'.\iota$.
--
--   A flat base change step inside the proper case of Grothendieck's existence theorem for coherent sheaves: the bound $N$ controlling both the annihilator of the kernel of the Čech unit map and the solvability of the $0$-cocycle equation, known over a larger affine open $W_0$ of $P$, is transported to a smaller affine open $W$ along the flat extension $R_0 \to R$ of the completed local frames. It is used in the derivation of the uniform threading statement [`AlgebraicGeometry.OModulePresheaf.exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_forall_smul_eq_zero_and_exists_eq_smul_of_le_of_flat_of_bijective.lean

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

theorem AlgebraicGeometry.OModulePresheaf.forall_smul_eq_zero_and_exists_eq_smul_of_le_of_flat_of_bijective
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

    (W₀ : P.affineOpens)
    (R₀ : Type u) [CommRing R₀] [Algebra Γ(P, W₀.1) R₀]
    (L₀ : Type u) [AddCommGroup L₀] [Module Γ(P, W₀.1) L₀] [Module R₀ L₀] [IsScalarTower Γ(P, W₀.1) R₀ L₀]
    [Module.Finite R₀ L₀]
    (pr₀ : ∀ n : ℕ, L₀ →ₗ[Γ(P, W₀.1)] (F n).obj W₀.1)
    (hprc₀ : ∀ (n : ℕ) (x : L₀), (φ n).app W₀ (pr₀ (n + 1) x) = pr₀ n x)
    (hpri₀ : ∀ x : L₀, (∀ n : ℕ, pr₀ n x = 0) → x = 0)
    (hprs₀ : ∀ n : ℕ, Function.Surjective (pr₀ n))
    (hprk₀ : ∀ n : ℕ, LinearMap.ker (pr₀ n) = (I.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ q.appLE ⊤ W₀.1 le_top).hom) ^ (n + 1) • (⊤ : Submodule Γ(P, W₀.1) L₀))

    {Y₀ : Scheme.{u}} (sY₀ : Y₀ ⟶ Spec (CommRingCat.of R₀)) [IsProper sY₀] (t₀ : Y₀ ⟶ V')
    (hY₀ : IsPullback t₀ sY₀ (g ≫ i) (Spec.map (CommRingCat.ofHom (algebraMap Γ(P, W₀.1) R₀)) ≫ W₀.2.fromSpec))
    (hta₀ : ∀ V : V'.affineOpens, V.1 ≤ (g ≫ i) ⁻¹ᵁ W₀.1 → IsAffineOpen (t₀ ⁻¹ᵁ V.1))

    (G₀ : OModulePresheaf sY₀) (hGc₀ : G₀.IsCoherent) (hGq₀ : G₀.IsQuasicoherent)
    (ε₀ : ∀ U : Y₀.Opens, L₀ →ₗ[R₀] G₀.obj U)
    (hεr₀ : ∀ (U U' : Y₀.Opens) (h : U ≤ U') (x : L₀), G₀.res h (ε₀ U' x) = ε₀ U x)
    (hεβ₀ : ∀ U : Y₀.affineOpens,
      letI := Scheme.TwoAffineOpenCover.algebraOfHom sY₀ U.1
      ∃ β₀ : Γ(Y₀, U.1) ⊗[R₀] L₀ ≃ₗ[Γ(Y₀, U.1)] G₀.obj U.1, ∀ x : L₀, β₀ (1 ⊗ₜ x) = ε₀ U.1 x)

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
      ∃ β : Γ(Y, U.1) ⊗[R] L ≃ₗ[Γ(Y, U.1)] G.obj U.1, ∀ x : L, β (1 ⊗ₜ x) = ε U.1 x)

    (hW : W.1 ≤ W₀.1)
    [Algebra R₀ R] [Module.Flat R₀ R]
    (hR : ∀ b : Γ(P, W₀.1),
      algebraMap R₀ R (algebraMap Γ(P, W₀.1) R₀ b) = algebraMap Γ(P, W.1) R ((P.presheaf.map (homOfLE hW).op).hom b))
    (e : R ⊗[R₀] L₀ →ₗ[R] L) (heb : Function.Bijective e)
    (he : ∀ (n : ℕ) (x₀ : L₀), pr n (e ((1 : R) ⊗ₜ x₀)) = (F n).res hW (pr₀ n x₀))
    (N : ℕ)

    (hk₀ : ∀ x : L₀, (∀ j : K'.ι, ε₀ (t₀ ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W₀.1 j)) x = 0) →
      ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W₀ ^ N, a • x = 0)
    (hc₀ : ∀ c : ∀ j : K'.ι, G₀.obj (t₀ ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W₀.1 j)),
      (∀ j j' : K'.ι,
          G₀.res ((Opens.map t₀.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W₀.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W₀.1 j') ≤ _)) (c j)
            = G₀.res ((Opens.map t₀.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W₀.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W₀.1 j') ≤ _)) (c j')) →
      ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W₀ ^ N,
        ∃ x : L₀, ∀ j : K'.ι, ε₀ (t₀ ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W₀.1 j)) x = algebraMap Γ(P, W₀.1) R₀ a • c j) :
    (∀ x : L, (∀ j : K'.ι, ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x = 0) →
      ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N, a • x = 0) ∧
    (∀ c : ∀ j : K'.ι, G.obj (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)),
      (∀ j j' : K'.ι,
          G.res ((Opens.map t.base).monotone (inf_le_left : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j)
            = G.res ((Opens.map t.base).monotone (inf_le_right : (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j) ⊓ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j') ≤ _)) (c j')) →
      ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N,
        ∃ x : L, ∀ j : K'.ι, ε (t ⁻¹ᵁ (OModulePresheaf.cechPushforward.chart (g ≫ i) K' W.1 j)) x = algebraMap Γ(P, W.1) R a • c j) := by sorry
