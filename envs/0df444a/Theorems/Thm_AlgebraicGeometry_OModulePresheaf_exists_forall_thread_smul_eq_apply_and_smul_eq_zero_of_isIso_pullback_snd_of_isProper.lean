-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/34fee77f-c99f-5de0-8274-7e5f89a14b5f
-- title:
--   Uniform annihilation of kernel and cokernel of the threaded Čech unit
-- statement:
--   Let $A$ be a Noetherian commutative ring, $I\subseteq A$ an ideal, $q:P\to\operatorname{Spec}A$ proper, $i:Z\to P$ a closed immersion, $g:V'\to Z$ proper, $K'$ an ordered affine cover of $V'$ (a finite linearly ordered family of affine opens with supremum $\top$), $U\subseteq Z$ open such that $\mathrm{pullback.snd}\,g\,U.\iota$ is an isomorphism, and $T'\subseteq P$ closed with $i(z)\in T'$ for every $z\notin U$. Let $F_k$ be $\mathcal O$-module presheaves over $q$, each coherent (finitely generated sections over affine opens) and quasicoherent in the sense of the two basic-open conditions, with $\mathrm{AffHom}$s $\varphi_k:F_{k+1}\to F_k$ surjective on every affine open and with kernel $I^{k+1}\cdot\top$ there, each $F_k$ annihilated by the ideal sheaf `i.ker`. Let $F'_k$ be presheaves over $(g\circ i)\circ q$ with maps $\varphi'_k$, together with $A$-linear $\eta$ from $F_k(U_0)$ to $F'_k(V)$ for affine opens $V\subseteq (g\circ i)^{-1}U_0$, semilinear over the appropriate restriction ring map, compatible with restriction in $V$ and in $U_0$ and with $\varphi_k,\varphi'_k$, and realising $F'_k(V)$ as $\Gamma(V',V)\otimes_{\Gamma(P,U_0)}F_k(U_0)$ via $x\mapsto 1\otimes x$. Let $v_k:F_k\to$ the Čech pushforward of $F'_k$ (cocycle families on the charts $K'_j\cap (g\circ i)^{-1}(-)$), with $j$-th component given by $\eta$ on the affine chart. Then for every affine open $W_0$ of $P$ there is $N$ such that for every affine open $W\subseteq W_0$ and every $a$ in the $N$-th power of the vanishing ideal of $T'$ on $W$: every thread $(\ell_n)$ compatible under the Čech pushforwards of the $\varphi'_n$ satisfies $v_n(m_n)=a\ell_n$ for some thread $(m_n)$ compatible under the $\varphi_n$; and any $\varphi$-compatible thread $(m_n)$ with all $v_n(m_n)=0$ satisfies $a\cdot m_n=0$ for all $n$.
--
--   This is the uniformity step in the proper case of Grothendieck's existence theorem: the unit from the $I$-adic system on $P$ to the Čech direct image of its inverse image along the proper cover $V'\to Z\hookrightarrow P$ has kernel and cokernel on threads annihilated by a single power of the ideal of $T'$, with the exponent $N$ uniform over affine opens inside a fixed $W_0$ and over the levels of the system. It feeds the step deducing that threads are, after multiplication by such elements, in the range of the unit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper.lean

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

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_thread_smul_eq_apply_and_smul_eq_zero_of_isIso_pullback_snd_of_isProper
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
            (OModulePresheaf.cechPushforward.chart_le_preimage (g ≫ i) K' U₀.1 j) x) :
    ∀ W₀ : P.affineOpens, ∃ N : ℕ, ∀ W : P.affineOpens, W.1 ≤ W₀.1 →
        (∀ (ℓ : ∀ n, (OModulePresheaf.cechPushforward (g ≫ i) q K' (F' n)).obj W.1),
          (∀ n, ((φ' n).cechPushforward (g ≫ i) q K').app W (ℓ (n + 1)) = ℓ n) →
          ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
            ∃ m : ∀ n, (F n).obj W.1,
              (∀ n, (φ n).app W (m (n + 1)) = m n) ∧ ∀ n, (v n).app W (m n) = a • ℓ n) ∧
        (∀ (m : ∀ n, (F n).obj W.1), (∀ n, (φ n).app W (m (n + 1)) = m n) →
          (∀ n, (v n).app W (m n) = 0) →
          ∀ a : Γ(P, W.1), a ∈ (Scheme.IdealSheafData.vanishingIdeal T').ideal W ^ N →
            ∀ n, a • m n = 0) := by sorry
