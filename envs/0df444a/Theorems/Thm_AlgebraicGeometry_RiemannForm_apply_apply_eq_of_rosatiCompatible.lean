-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_apply_apply_eq_of_rosatiCompatible
-- name    : AlgebraicGeometry.RiemannForm.apply_apply_eq_of_rosatiCompatible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/23277d1d-8554-5af3-9caa-2440e608187f
-- title:
--   Rosati adjointness of ι(b^⋆) for the Riemann form
-- statement:
--   Let $k$ be an algebraically closed field, let $A$ be a scheme with a morphism $f : A \to \operatorname{Spec} k$, and let $L$ be a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f \text{-over } t\}$ of points over arbitrary $k$-schemes $t : T \to \operatorname{Spec} k$, assumed commutative via `hc`; `hA` records that $f$ is smooth and proper with connected fibres and carries a relative group law. Let $\mathcal L$ be a module on $A$ that is invertible (locally on $A$ isomorphic to the unit), let $\ell$ be a prime invertible in $k$, and let $\zeta : \mathbb N \to k$ be such that each $\zeta(n)$ is a primitive $\ell^n$-th root of unity and $\zeta(n+1)^{\ell} = \zeta(n)$. Let $e$ be a $\mathbb Z_\ell$-bilinear form on the Tate module of the group of $k$-points, the group of sequences $(x_n)$ of $k$-points with $\ell^n x_n = 0$ and $\ell x_{n+1} = x_n$, and assume `he`: for all $n$ and all $a,b$, the element $\zeta(n)^{(e\,a\,b).\mathrm{appr}\,n}$ is a level-$\ell^n$ pairing value of the $n$-th components of $a$ and $b$ with respect to $\mathcal L$. Let $I$ be a type, $\mathrm{act} : I \to (A \to A)$ with each $\mathrm{act}\,b$ a morphism over $f$, and $\star : I \to I$; assume `hιhom`: pushing points forward along $\mathrm{act}\,b$ is a homomorphism for the group law at every base point, and `hR` (Rosati compatibility): for each $b$, the pullbacks of the Mumford bundle $m^*\mathcal L \otimes (p_1^*\mathcal L^{\vee} \otimes p_2^*\mathcal L^{\vee})$ on $A \times_k A$ along $(p_1, \mathrm{act}\,b \circ p_2)$ and along $(\mathrm{act}(b^\star) \circ p_1, p_2)$ are isomorphic locally over the base. Finally let $T : I \to \operatorname{End}_{\mathbb Z_\ell}$ of the Tate module satisfy `hT`: for every $b$, $a$ and $n$, the $n$-th point of $T\,b\,a$ is the push-forward along $\mathrm{act}\,b$ of the $n$-th point of $a$. Then for every $b \in I$ and all $a, c$ in the Tate module, $e(T(b^\star)a, c) = e(a, T(b)c)$.
--
--   This is the statement that Rosati compatibility of $\mathcal L$ with a family of endomorphisms, through the map $\star$, makes $\iota(b^\star)$ the adjoint of $\iota(b)$ for the $\ell$-adic Riemann form attached to $\mathcal L$. It is the form in which the quaternionic (and Hecke) action is shown to be self-adjoint up to $\star$ on the Tate module; the variant for involutive $\star$ is deduced from it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_apply_apply_eq_of_rosatiCompatible.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm AlgebraicGeometry.Polarisation CerednikDrinfeld.QM

theorem AlgebraicGeometry.RiemannForm.apply_apply_eq_of_rosatiCompatible
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (ζ : ℕ → k) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n)
    (e : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he : IsRiemannForm f L hc 𝓛 ℓ ζ e)
    {I : Type} (act : I → (A ⟶ A)) (act_over : ∀ b : I, act b ≫ f = f) (star : I → I)
    (hιhom : ∀ (b : I) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (P Q : SchemeHomOver t f),
      pushPt (act b) (act_over b) (L.mul t P Q) = L.mul t (pushPt (act b) (act_over b) P) (pushPt (act b) (act_over b) Q))
    (hR : RosatiCompatible f L 𝓛 act act_over star)
    (T : I → (TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k)))
    (hT : ∀ (b : I) (a : TateModule ℓ (L.AlgPoints hc k)) (n : ℕ),
      RelativeGroupLaw.AlgPoints.toPoint ((T b a : ℕ → L.AlgPoints hc k) n) =
        pushPt (act b) (act_over b) (RelativeGroupLaw.AlgPoints.toPoint ((a : ℕ → L.AlgPoints hc k) n)))
    (b : I) (a c : TateModule ℓ (L.AlgPoints hc k)) :
    e (T (star b) a) c = e a (T b c) := by sorry
