-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward
-- name    : AlgebraicGeometry.OModulePresheaf.exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/9eef9a8b-3fe9-5465-a67b-ddafd3fe86b7
-- title:
--   Thread-level bounds imply level-wise bounds for u_k
-- statement:
--   Let $A$ be a Noetherian commutative ring, $I \subseteq A$ an ideal, $q : P \to \operatorname{Spec} A$ a proper morphism of schemes, $i : Z \to P$ a closed immersion, $g : V' \to Z$ proper, and $K'$ an ordered affine cover of $V'$ (a finite, linearly ordered family of affine opens with supremum $\top$). Let $U$ be an open of $Z$ over which $g$ is an isomorphism, in the sense that the second projection of the pullback of $g$ along $U \hookrightarrow Z$ is an isomorphism, and let $T'$ be a closed subset of $P$ with $i(z) \in T'$ for every $z \notin U$; write $\mathcal J$ for the vanishing ideal sheaf data of $T'$. The data are: an $I$-adic system $(F_k, \varphi_k)$ of $\mathcal O$-module presheaves on $P$ over $q$, each $F_k$ coherent (finite over $\Gamma(P,W)$ on affine opens $W$) and quasi-coherent (the two localisation conditions on basic opens), with each $\varphi_k : F_{k+1} \to F_k$ an affine-open-level $A$-linear, $\Gamma$-semilinear map compatible with restrictions, surjective on affine opens and with kernel $I^{k+1} F_{k+1}(W)$, and with each $F_k$ annihilated by the ideal sheaf data $i$`.ker` (so carried by $Z$); a system $(F'_k, \varphi'_k)$ on $V'$ over $(g \circ i) \circ q$ together with comparison maps $\eta$ from $F_k(W)$ to $F'_k(V)$ for affine opens $V \subseteq (g\circ i)^{-1}W$, semilinear for `appLE`, compatible with restriction in $V$ and in $W$, compatible with $\varphi$ and $\varphi'$, and inducing $\Gamma(V',V)$-linear isomorphisms $\Gamma(V',V) \otimes_{\Gamma(P,W)} F_k(W) \cong F'_k(V)$ taking $1 \otimes x$ to $\eta(x)$; a coherent quasi-coherent $G'$ on $V'$ with surjections $\psi'_k : G' \to F'_k$ of kernel $I^{k+1}G'$, compatible with the $\varphi'_k$; maps $v_k : F_k \to (g\circ i)_*F'_k$ into the Čech pushforward along $K'$, whose sections over $W$ are the tuples $(x_j)_j$ with $x_j \in F'_k(K'.U_j \cap (g\circ i)^{-1}W)$ agreeing on pairwise intersections, with components given by $\eta$; and comparison data $(Ps_k, \pi_k, \psi^P_k, \nu_k, u_k)$, consisting of an $I$-adic system $(Ps_k,\pi_k)$ of coherent quasi-coherent presheaves on $P$ with surjective transition maps of kernel $I^{k+1}$, surjections $\psi^P_k$ from the Čech pushforward of $G'$ onto $Ps_k$ of kernel $I^{k+1}$ compatible with $\pi$, maps $\nu_k : Ps_k \to (g\circ i)_*F'_k$ compatible with $\pi_k$ and the pushforward of $\varphi'_k$ and satisfying $\nu_k \circ \psi^P_k = (g\circ i)_*\psi'_k$, an Artin–Rees bound stating that for every affine open $W$ and every $k$ there is $c$ with $\ker(\nu_{k+c})(W) \subseteq I^{k+1}Ps_{k+c}(W)$, and maps $u_k : F_k \to Ps_k$ compatible with $\varphi$ and $\pi$ and satisfying $\nu_k \circ u_k = v_k$ (these hypotheses are summarised here). Assume finally the thread-level bound: there is $N$ such that over every affine open $W$ of $P$, first, every compatible sequence $(\ell_n)$ with $\ell_n \in ((g\circ i)_*F'_n)(W)$ and every $a \in \mathcal J(W)^N$ admit a compatible sequence $(m_n)$ in the $F_n(W)$ with $v_n(m_n) = a \cdot \ell_n$ for all $n$, and second, every compatible sequence $(m_n)$ with all $v_n(m_n) = 0$ satisfies $a \cdot m_n = 0$ for all $n$ and all $a \in \mathcal J(W)^N$. The conclusion is that there is $N$ such that: for all $k$, every affine open $W$ of $P$, every $a \in \mathcal J(W)^N$ and every $y \in Ps_k(W)$ there is $x \in F_k(W)$ with $u_k(x) = a \cdot y$; and for every affine open $W$ there is $c$ such that for all $k$, every $x \in F_{k+c}(W)$ with $u_{k+c}(x) = 0$ and every $a \in \mathcal J(W)^N$ satisfy $a \cdot x \in I^{k+1}F_{k+c}(W)$.
--
--   This is the assembly step in the discrepancy-localisation argument for Grothendieck's existence theorem in the proper case: it converts bounds on inverse limits of sections (threads) over affine opens, uniform in the open, into the level-wise cokernel and kernel bounds for the comparison maps $u_k$, with the vanishing ideal of $T'$ supplying the multipliers. It is used by [`AlgebraicGeometry.OModulePresheaf.exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_forall_smul_mem_range_of_cechPushforward_of_isIso_pullback_snd_of_isProper), and its proof cites the kernel–cokernel statement for $I$-adic systems of coherent presheaves on $P$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward.lean

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

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_smul_mem_range_of_forall_thread_of_cechPushforward
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
    (hνu : ∀ (k : ℕ) (W : P.affineOpens), (ν k).app W ∘ₗ (u k).app W = (v k).app W)

    (hunif : ∃ N : ℕ, ∀ W : P.affineOpens,
      (∀ (ℓ : ∀ n, (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' n)).obj W.1),
        (∀ n, ((φ' n).cechPushforward (g ≫ i) q K').app W (ℓ (n + 1)) = ℓ n) →
        ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
          ∃ m : ∀ n, (F n).obj W.1,
            (∀ n, (φ n).app W (m (n + 1)) = m n) ∧ ∀ n, (v n).app W (m n) = a • ℓ n) ∧
      (∀ (m : ∀ n, (F n).obj W.1), (∀ n, (φ n).app W (m (n + 1)) = m n) →
        (∀ n, (v n).app W (m n) = 0) →
        ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
          ∀ n, a • m n = 0)) :
    ∃ N : ℕ,
      (∀ (k : ℕ) (W : P.affineOpens) (a : Γ(P, W.1)),
        a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
        ∀ y : (Ps k).obj W.1, ∃ x : (F k).obj W.1, (u k).app W x = a • y) ∧
      (∀ W : P.affineOpens, ∃ c : ℕ, ∀ (k : ℕ) (x : (F (k + c)).obj W.1), (u (k + c)).app W x = 0 →
        ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
          a • x ∈ I ^ (k + 1) • (⊤ : Submodule A ((F (k + c)).obj W.1))) := by sorry
