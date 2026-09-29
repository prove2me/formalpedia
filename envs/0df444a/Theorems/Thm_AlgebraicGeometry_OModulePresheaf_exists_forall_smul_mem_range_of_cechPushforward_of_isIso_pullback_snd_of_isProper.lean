-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/82ddfa2a-710e-5994-84ce-4aa9029867db
-- title:
--   Cokernel and kernel of ̂ u killed by a power of J
-- statement:
--   Let $A$ be a Noetherian commutative ring, $I\subseteq A$ an ideal, $q\colon P\to\operatorname{Spec}A$ proper, $i\colon Z\to P$ a closed immersion, $g\colon V'\to Z$ proper, $K'$ a finite linearly ordered affine open cover of $V'$, $U$ an open of $Z$ for which the second projection of the fibre product of $g$ with $U\hookrightarrow Z$ is an isomorphism, and $T'$ a closed subset of $P$ containing $i(z)$ for every $z\notin U$; write $p'$ for $g$ followed by $i$. The data are: a sequence $F_k$ of presheaves of modules over $q$ (each open of $P$ carries an $A$-module with a compatible $\Gamma(P,\cdot)$-action and restriction maps), coherent (finite over $\Gamma(P,W)$ on affine $W$) and quasi-coherent (the basic-open localisation and torsion conditions), with affine-open morphisms $\varphi_k\colon F_{k+1}\to F_k$ surjective with kernel $I^{k+1}F_{k+1}(W)$, each $F_k$ annihilated by the ideal of `i.ker`; a system $F'_k$ over $p'$ followed by $q$ with $\varphi'_k$, together with $A$-linear maps $\eta$ from $F_k(U_0)$ to $F'_k(V)$ for affine $V\subseteq p'^{-1}U_0$ that are semilinear over $\Gamma(P,U_0)\to\Gamma(V',V)$, compatible with restriction in $V$ and in $U_0$ and with the $\varphi$'s, and inducing isomorphisms $\Gamma(V',V)\otimes_{\Gamma(P,U_0)}F_k(U_0)\cong F'_k(V)$; a coherent quasi-coherent $G'$ on $V'$ with $\psi'_k\colon G'\to F'_k$ surjective, of kernel $I^{k+1}G'(V)$, compatible with $\varphi'_k$; morphisms $v_k$ from $F_k$ into the Čech pushforward of $F'_k$ along $p'$ relative to $K'$ (the module of $0$-cocycles on the charts $K'_j\cap p'^{-1}W$) given componentwise by $\eta$; a coherent quasi-coherent system $Ps_k$ with $\pi_k$ surjective of kernel $I^{k+1}$, surjections $\psi P_k$ from the Čech pushforward of $G'$ onto $Ps_k$ with kernel $I^{k+1}$ compatible with $\pi_k$, comparison maps $\nu_k\colon Ps_k\to$ the Čech pushforward of $F'_k$ commuting with the $\pi_k$ and the pushed-forward $\varphi'_k$ and satisfying $\nu_k\circ\psi P_k=$ the pushforward of $\psi'_k$, with the Artin–Rees-type property that for each affine $W$ and each $k$ some $c$ gives $\ker\nu_{k+c}(W)\subseteq I^{k+1}Ps_{k+c}(W)$; and morphisms $u_k\colon F_k\to Ps_k$ with $\pi_k\circ u_{k+1}=u_k\circ\varphi_k$ and $\nu_k\circ u_k=v_k$. The conclusion: there is an $N$, independent of $k$ and of the affine open, such that, writing $\mathcal J$ for the vanishing ideal of $T'$, (i) for every $k$, every affine open $W$ of $P$, every $a\in\mathcal J(W)^N$ and every $y\in Ps_k(W)$ there is $x\in F_k(W)$ with $u_k(x)=a\cdot y$; and (ii) for every affine open $W$ there is $c$ such that for all $k$, every $x\in F_{k+c}(W)$ with $u_{k+c}(x)=0$ and every $a\in\mathcal J(W)^N$ satisfy $a\cdot x\in I^{k+1}F_{k+c}(W)$.
--
--   This is the localisation step in Grothendieck's existence theorem for proper morphisms: the comparison map from a formal coherent system to the direct image of its algebraised pull-back along a proper modification that is an isomorphism over $U$ has kernel and cokernel annihilated by a fixed power of the ideal of a closed set containing the complement of $U$, uniformly in the level $k$. It feeds the construction of a coherent module on $P$ with prescribed $I$-adic quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper
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

    (G' : OModulePresheaf ((g ≫ i) ≫ q)) (hG'c : G'.IsCoherent) (hG'q : G'.IsQuasicoherent)
    (ψ' : ∀ k, OModulePresheaf.AffHom G' (F' k))
    (hψ's : ∀ (k : ℕ) (V : V'.affineOpens), Function.Surjective ((ψ' k).app V))
    (hψ'k : ∀ (k : ℕ) (V : V'.affineOpens),
      LinearMap.ker ((ψ' k).app V) = I ^ (k + 1) • (⊤ : Submodule A (G'.obj V.1)))
    (hψ'c : ∀ (k : ℕ) (V : V'.affineOpens), (φ' k).app V ∘ₗ (ψ' (k + 1)).app V = (ψ' k).app V)

    (v : ∀ k, OModulePresheaf.AffHom (F k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hvη : ∀ (k : ℕ) (U₀ : P.affineOpens) (x : (F k).obj U₀.1) (j : K'.ι),
      ((v k).app U₀ x).1 j
        = η k U₀ (OModulePresheaf.AffHom.affineChart (g ≫ i) q K' U₀ j)
            (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' U₀.1 j) x)

    (Ps : ℕ → OModulePresheaf q) (hPsc : ∀ k, (Ps k).IsCoherent) (hPsq : ∀ k, (Ps k).IsQuasicoherent)
    (π : ∀ k, OModulePresheaf.AffHom (Ps (k + 1)) (Ps k))
    (hπs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((π k).app U))
    (hπk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((π k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + 1)).obj U.1)))
    (ψP : ∀ k, OModulePresheaf.AffHom (OModulePresheaf.cechPushforward (g ≫ i) q K' G') (Ps k))
    (hψPs : ∀ (k : ℕ) (W : P.affineOpens), Function.Surjective ((ψP k).app W))
    (hψPk : ∀ (k : ℕ) (W : P.affineOpens),
      LinearMap.ker ((ψP k).app W)
        = I ^ (k + 1) • (⊤ : Submodule A ((OModulePresheaf.cechPushforward (g ≫ i) q K' G').obj W.1)))
    (hψPc : ∀ (k : ℕ) (W : P.affineOpens), (π k).app W ∘ₗ (ψP (k + 1)).app W = (ψP k).app W)
    (ν : ∀ k, OModulePresheaf.AffHom (Ps k) (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' k)))
    (hνc : ∀ (k : ℕ) (W : P.affineOpens),
      ((φ' k).cechPushforward (g ≫ i) q K').app W ∘ₗ (ν (k + 1)).app W = (ν k).app W ∘ₗ (π k).app W)
    (hνψP : ∀ (k : ℕ) (W : P.affineOpens),
      (ν k).app W ∘ₗ (ψP k).app W = ((ψ' k).cechPushforward (g ≫ i) q K').app W)
    (hνi : ∀ (W : P.affineOpens) (k : ℕ), ∃ c : ℕ,
      LinearMap.ker ((ν (k + c)).app W) ≤ I ^ (k + 1) • (⊤ : Submodule A ((Ps (k + c)).obj W.1)))
    (u : ∀ k, OModulePresheaf.AffHom (F k) (Ps k))
    (huc : ∀ (k : ℕ) (W : P.affineOpens), (π k).app W ∘ₗ (u (k + 1)).app W = (u k).app W ∘ₗ (φ k).app W)
    (hνu : ∀ (k : ℕ) (W : P.affineOpens), (ν k).app W ∘ₗ (u k).app W = (v k).app W) :
    ∃ N : ℕ,
      (∀ (k : ℕ) (W : P.affineOpens) (a : Γ(P, W.1)),
        a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
        ∀ y : (Ps k).obj W.1, ∃ x : (F k).obj W.1, (u k).app W x = a • y) ∧
      (∀ W : P.affineOpens, ∃ c : ℕ, ∀ (k : ℕ) (x : (F (k + c)).obj W.1), (u (k + c)).app W x = 0 →
        ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
          a • x ∈ I ^ (k + 1) • (⊤ : Submodule A ((F (k + c)).obj W.1))) := by sorry
