-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_perfect_of_forall_torsion_kernelPts_eq_zero
-- name    : AlgebraicGeometry.RiemannForm.perfect_of_forall_torsion_kernelPts_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/a740d7d3-7aed-5a4c-b0b6-fe508bccd674
-- title:
--   Perfectness of the Riemann form on T_ℓ A
-- statement:
--   Let $k$ be an algebraically closed field, $f : A \to \operatorname{Spec} k$ a morphism of schemes, and $L$ a relative group law on $f$ (functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} k$, compatible with base change) which is commutative, $hc$. Assume the bundle `AbelianSchemePropertyBundle k f`: $f$ is smooth and proper with connected fibres and admits a relative group law. Let $\mathcal L$ be a module on $A$ that is invertible in the sense that every point of $A$ has an open neighbourhood $U$ on which the pullback of $\mathcal L$ along $U \hookrightarrow A$ is isomorphic to the unit sheaf, and let $g$ be a natural number such that every fibre $f^{-1}(s)$ has topological Krull dimension $g$. Let $\ell$ be prime with $\ell \neq 0$ in $k$, and $\zeta : \mathbb N \to k$ a compatible system of primitive $\ell^n$-th roots of unity, i.e. $\zeta(n)$ is a primitive $\ell^n$-th root of unity and $\zeta(n+1)^\ell = \zeta(n)$. Let $e$ be a $\mathbb Z_\ell$-bilinear form on the Tate module $T_\ell = \{x : \mathbb N \to A(k) \mid \ell^n \cdot x_n = 0,\ \ell \cdot x_{n+1} = x_n\}$ of the group $A(k)$ of $k$-points of $L$, and suppose $e$ is a Riemann form for $\mathcal L$: for all $n$ and all $a, b \in T_\ell$, the level-$\ell^n$ pairing value of $(a_n, b_n)$ against $\mathcal L$ is $\zeta(n)^{(e\,a\,b).\mathrm{appr}\,n}$, where the level-$n$ pairing value of $(x,y)$ being $c$ means that translation by $x$ fixes the multiplication-by-$n$ morphism of $A$ and that, for some isomorphism $\beta$ between the pullbacks along $[n]$ of $T_y^*\mathcal L$ and of $\mathcal L$, the composite automorphism built from $\beta$, its transport along translation by $x$, and the identifications coming from $[n]$, is multiplication by the constant $c$. Finally assume $hK$: every $\ell$-power-torsion point $Q \in A(k)$ (i.e. $\ell^n \cdot Q = 0$ for some $n$) with $T_Q^*\mathcal L \cong \mathcal L$ is zero. Then $e$ is a perfect pairing, i.e. both currying maps $T_\ell \to \operatorname{Hom}_{\mathbb Z_\ell}(T_\ell, \mathbb Z_\ell)$ are bijective.
--
--   This is the nondegeneracy statement for the Riemann (Weil) form attached to an invertible sheaf $\mathcal L$ on an abelian variety over an algebraically closed field: triviality of the $\ell$-power torsion of the group $K(\mathcal L)$ of translations preserving $\mathcal L$ forces the $\ell$-adic form to be a perfect $\mathbb Z_\ell$-pairing. It is used in the treatment of fake elliptic curves arising from quaternionic multiplication, where the perfectness of the form is combined with Rosati compatibility.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_perfect_of_forall_torsion_kernelPts_eq_zero.lean

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

theorem AlgebraicGeometry.RiemannForm.perfect_of_forall_torsion_kernelPts_eq_zero
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (ζ : ℕ → k) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n)
    (e : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he : IsRiemannForm f L hc 𝓛 ℓ ζ e)
    (hK : ∀ (n : ℕ) (Q : L.AlgPoints hc k), ℓ ^ n • Q = 0 →
      Nonempty ((Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).obj 𝓛 ≅ 𝓛) → Q = 0) :
    e.IsPerfPair := by sorry
