-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/b10e7a39-7482-50c1-968f-6fc116c1da4f
-- title:
--   Globalising the exponent for Čech thread comparison over P
-- statement:
--   Fix a Noetherian commutative ring $A$ and an ideal $I \subseteq A$, a proper morphism $q : P \to \operatorname{Spec} A$, a closed immersion $i : Z \to P$, a proper morphism $g : V' \to Z$, and an ordered affine cover $K'$ of $V'$ (a finite linearly ordered index set together with affine opens covering $V'$); further an open $U \subseteq Z$ such that the second projection of the pullback of $g$ along $U \hookrightarrow Z$ is an isomorphism, and a closed set $T' \subseteq P$ containing $i(z)$ for every $z \notin U$. The data on $P$ are presheaves $F_k$ of $A$-modules on the opens of $P$, each $F_k(U_0)$ also a $\Gamma(P,U_0)$-module compatibly, with restriction maps; each $F_k$ is coherent ($F_k(U_0)$ is a finite $\Gamma(P,U_0)$-module for affine $U_0$) and quasi-coherent (the usual basic-open criterion for sections and for torsion), each is annihilated by the ideal of `i.ker` on every affine open, and maps $\varphi_k : F_{k+1} \to F_k$ are given on affine opens, $\Gamma$-semilinear and compatible with restriction, surjective on each affine open with kernel $I^{k+1} F_{k+1}(U_0)$. On $V'$ are presheaves $F'_k$ for $(g \circ i) \circ q$ with maps $\varphi'_k : F'_{k+1} \to F'_k$, together with comparison maps $\eta_k : F_k(U_0) \to F'_k(V)$, $A$-linear, for affine $V \subseteq (g \circ i)^{-1}U_0$, semilinear over the transition map $\Gamma(P,U_0) \to \Gamma(V',V)$, compatible with shrinking $V$, with shrinking $U_0$, and with $\varphi_k, \varphi'_k$, and such that the induced map $\Gamma(V',V) \otimes_{\Gamma(P,U_0)} F_k(U_0) \to F'_k(V)$ is an isomorphism of $\Gamma(V',V)$-modules carrying $1 \otimes x$ to $\eta_k(x)$. Finally, maps $v_k$ from $F_k$ to the Čech pushforward of $F'_k$ along $g \circ i$ relative to $K'$ (whose sections over $U_0$ are the families, indexed by $K'$, of sections of $F'_k$ over $K'_j \cap (g \circ i)^{-1}U_0$ agreeing on pairwise intersections) are given, with $j$-th component of $v_k(x)$ equal to $\eta_k(x)$ on the corresponding chart. Writing $\mathcal{J}$ for the vanishing ideal of $T'$, and calling a thread over an affine $W$ a compatible system $(m_n)$ with $\varphi_n(m_{n+1}) = m_n$, the hypothesis is that every affine open $W_0 \subseteq P$ admits an $N$ such that for all affine $W \subseteq W_0$: every thread $\ell$ of the Čech pushforwards and every $a \in \mathcal{J}(W)^N$ admit a thread $m$ of $(F_n)$ over $W$ with $v_n(m_n) = a \ell_n$ for all $n$; and every thread $m$ with all $v_n(m_n) = 0$ satisfies $a m_n = 0$ for all $a \in \mathcal{J}(W)^N$ and all $n$. The conclusion is that a single $N$ has both properties for every affine open $W$ of $P$.
--
--   This is the gluing step in the proper case of the Grothendieck existence theorem (EGA III₁ 5.3.3): quasi-compactness of $P$ turns a local choice of exponent, made on each affine open of the base, into one exponent valid on all affine opens, for the comparison between threads of the $I$-adic system on $P$ and threads of its Čech direct image from $V'$. It feeds the statement that the Čech comparison map has image containing a power of the ideal of $T'$ times all threads, used in the induction establishing algebraisation of formal coherent data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper.lean

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

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_affineOpens_thread_smul_of_forall_exists_forall_le_of_isProper
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
    (hloc : ∀ W₀ : P.affineOpens, ∃ N : ℕ, ∀ W : P.affineOpens, W.1 ≤ W₀.1 →
      (∀ (ℓ : ∀ n, (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' n)).obj W.1),
        (∀ n, ((φ' n).cechPushforward (g ≫ i) q K').app W (ℓ (n + 1)) = ℓ n) →
        ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
          ∃ m : ∀ n, (F n).obj W.1,
            (∀ n, (φ n).app W (m (n + 1)) = m n) ∧ ∀ n, (v n).app W (m n) = a • ℓ n) ∧
      (∀ (m : ∀ n, (F n).obj W.1), (∀ n, (φ n).app W (m (n + 1)) = m n) →
        (∀ n, (v n).app W (m n) = 0) →
        ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
          ∀ n, a • m n = 0)) :
    ∃ N : ℕ, ∀ W : P.affineOpens,
      (∀ (ℓ : ∀ n, (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' n)).obj W.1),
        (∀ n, ((φ' n).cechPushforward (g ≫ i) q K').app W (ℓ (n + 1)) = ℓ n) →
        ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
          ∃ m : ∀ n, (F n).obj W.1,
            (∀ n, (φ n).app W (m (n + 1)) = m n) ∧ ∀ n, (v n).app W (m n) = a • ℓ n) ∧
      (∀ (m : ∀ n, (F n).obj W.1), (∀ n, (φ n).app W (m (n + 1)) = m n) →
        (∀ n, (v n).app W (m n) = 0) →
        ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
          ∀ n, a • m n = 0) := by sorry
