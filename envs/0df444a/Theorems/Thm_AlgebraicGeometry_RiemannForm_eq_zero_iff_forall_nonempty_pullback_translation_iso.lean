-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_eq_zero_iff_forall_nonempty_pullback_translation_iso
-- name    : AlgebraicGeometry.RiemannForm.eq_zero_iff_forall_nonempty_pullback_translation_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/614c418f-bc0c-52c1-8f9b-68468b0a5503
-- title:
--   Riemann form vanishes iff all translates of L are isomorphic
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a morphism, equipped with a relative group law $L$, i.e. a functorially compatible group structure on the sets of sections of $f$ over arbitrary $k$-schemes, assumed commutative by $hc$. Assume the bundle of properties $hA$: $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\mathcal{L}$ be a module on $A$ which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ on which the pullback of $\mathcal{L}$ along $U \hookrightarrow A$ is isomorphic to the unit module, and let $g$ be a natural number such that every fibre $f^{-1}(s)$ has topological Krull dimension $g$. Let $\ell$ be a prime which is nonzero in $k$, and let $\zeta : \mathbb{N} \to k$ be a compatible system of roots of unity: $\zeta_n$ is a primitive $\ell^n$-th root of unity and $\zeta_{n+1}^{\ell} = \zeta_n$. Write $A(k)$ for the additive group `L.AlgPoints hc k` of sections of $f$ over $\operatorname{Spec} k$, and let $T =$ [`TateModule ℓ (L.AlgPoints hc k)`](def/EllipticCurve_TateModule.html#L15) be the group of sequences $(x_n)$ in $A(k)$ with $\ell^n x_n = 0$ and $\ell x_{n+1} = x_n$. Finally let $e : T \times T \to \mathbb{Z}_\ell$ be $\mathbb{Z}_\ell$-bilinear and assume `IsRiemannForm`: for all $n$ and all $a, b \in T$, the value $\zeta_n^{\,\mathrm{appr}_n(e(a,b))}$ is the level-$\ell^n$ pairing value of the pair $(a_n, b_n)$ attached to $\mathcal{L}$, that is, translation by $a_n$ fixes the multiplication-by-$\ell^n$ morphism and there is an isomorphism $\beta$ between the pullbacks along that morphism of the translate of $\mathcal{L}$ by $b_n$ and of $\mathcal{L}$ for which the resulting automorphism is multiplication by that constant. The conclusion: $e = 0$ if and only if for every $Q \in A(k)$ the pullback of $\mathcal{L}$ along translation by $Q$ is isomorphic to $\mathcal{L}$.
--
--   This identifies the kernel of the construction sending an invertible sheaf to its $\ell$-adic Riemann form: the form vanishes exactly when $\mathcal{L}$ lies in $\operatorname{Pic}^0$, i.e. $K(\mathcal{L})$ is everything. It is used in the Cerednik–Drinfeld/fake elliptic curve part of the development, where vanishing of a Riemann form has to be converted into translation-invariance of a line bundle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_eq_zero_iff_forall_nonempty_pullback_translation_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.eq_zero_iff_forall_nonempty_pullback_translation_iso
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (ζ : ℕ → k) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n)
    (e : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he : IsRiemannForm f L hc 𝓛 ℓ ζ e) :
    e = 0 ↔ ∀ Q : L.AlgPoints hc k,
      Nonempty ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛 ≅ 𝓛) := by sorry
