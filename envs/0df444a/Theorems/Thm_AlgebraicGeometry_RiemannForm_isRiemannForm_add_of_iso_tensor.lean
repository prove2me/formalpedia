-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_isRiemannForm_add_of_iso_tensor
-- name    : AlgebraicGeometry.RiemannForm.isRiemannForm_add_of_iso_tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/6e49c471-2741-59b8-bbfd-275489f3d35f
-- title:
--   Additivity of the Riemann form in the line bundle
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$, and let $L$ be a relative group law on $f$ (a group structure on the sets $\operatorname{SchemeHomOver} t\,f$ of $T$-points of $A$ over $\operatorname{Spec} k$, natural in $T$), assumed commutative by `hc`. Assume `hA`: $f$ is smooth and proper, each fibre of $f$ over a point of $\operatorname{Spec} k$ is connected, and $f$ carries a relative group law. Let $\mathcal L$ be a module on $A$ that is invertible in the sense that every point has an open neighbourhood $U$ on which the pullback of $\mathcal L$ along $U \hookrightarrow A$ is isomorphic to the unit sheaf of $U$. Let $\ell$ be a prime with $\ell \neq 0$ in $k$, and let $\zeta : \mathbb N \to k$ satisfy that $\zeta_n$ is a primitive $\ell^n$-th root of unity for every $n$, together with the compatibility $\zeta_{n+1}^{\ell} = \zeta_n$. Write $T_\ell$ for the Tate module of the group of $k$-points of $L$, namely the group of sequences $(x_n)$ with $\ell^n x_n = 0$ and $\ell x_{n+1} = x_n$. Let $e, e' : T_\ell \times T_\ell \to \mathbb Z_\ell$ be $\mathbb Z_\ell$-bilinear maps satisfying `IsRiemannForm` for $\mathcal L$, respectively for a second invertible module $\mathcal M$: for all $n$ and all $a, b \in T_\ell$, the scalar $\zeta_n^{(e\,a\,b).\mathrm{appr}\,n}$ (respectively with $e'$ and $\mathcal M$) is a level pairing value of the bundle at level $\ell^n$ for the $k$-points $a_n$ and $b_n$. Let $\mathcal N$ be a module on $A$ admitting an isomorphism $\mathcal N \cong \mathcal L \otimes \mathcal M$. Then $e + e'$ satisfies `IsRiemannForm` for $\mathcal N$.
--
--   This is the additivity of the Riemann form in the line bundle, $e^{\mathcal L \otimes \mathcal M} = e^{\mathcal L} + e^{\mathcal M}$, in the form needed for the $\ell$-adic pairing attached to an invertible module on an abelian scheme over an algebraically closed field. It is used in the construction of polarisation data for fake elliptic curves, where the Riemann form of a tensor product of a bundle with its pullback under inversion is compared with twice the original form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_isRiemannForm_add_of_iso_tensor.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm MonoidalCategory

theorem AlgebraicGeometry.RiemannForm.isRiemannForm_add_of_iso_tensor
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (ζ : ℕ → k) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n)
    (e : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he : IsRiemannForm f L hc 𝓛 ℓ ζ e)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (e' : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he' : IsRiemannForm f L hc 𝓜 ℓ ζ e')
    (𝓝 : A.Modules) (h𝓝 : Nonempty (𝓝 ≅ 𝓛 ⊗ 𝓜)) :
    IsRiemannForm f L hc 𝓝 ℓ ζ (e + e') := by sorry
