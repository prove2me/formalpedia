-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_isRiemannForm_swap_eq_neg_and_self_eq_zero
-- name    : AlgebraicGeometry.RiemannForm.isRiemannForm_swap_eq_neg_and_self_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/0bc4163f-c1b8-589d-aa97-3b1a14ef96f6
-- title:
--   Skew-symmetry and vanishing on the diagonal of a Riemann form
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme and $f : A \to \operatorname{Spec} k$, and let $L$ be a relative group law for $f$ over $k$, that is, a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ t = f\}$ of $T$-points over each $t : T \to \operatorname{Spec} k$, natural in $T$; assume $L$ is commutative. Assume further the bundle of properties asserting that $f$ is smooth and proper, that every fibre of $f$ is connected, and that a relative group law for $f$ exists. Let $\mathcal{L}$ be a module on $A$ which is invertible, in the sense that every point of $A$ has an open neighbourhood $U$ such that the pullback of $\mathcal{L}$ along $U \hookrightarrow A$ is isomorphic to the unit sheaf of $U$. Let $\ell$ be a prime with $\ell \neq 0$ in $k$, and let $\zeta : \mathbb{N} \to k$ be a compatible system of roots of unity: $\zeta_n$ is a primitive $\ell^n$-th root of unity and $\zeta_{n+1}^{\ell} = \zeta_n$. Write $T_\ell$ for the Tate module of the additive group of $k$-points of $L$, the group of sequences $x : \mathbb{N} \to L.\mathrm{AlgPoints}$ with $\ell^n \cdot x_n = 0$ and $\ell \cdot x_{n+1} = x_n$. Let $e : T_\ell \times T_\ell \to \mathbb{Z}_\ell$ be $\mathbb{Z}_\ell$-bilinear and suppose $e$ is a Riemann form for $\mathcal{L}$: for all $n$ and all $a, b \in T_\ell$, the scalar $\zeta_n^{\,(e\,a\,b).\mathrm{appr}\,n}$ is a level-$\ell^n$ pairing value of $\mathcal{L}$ at the pair of points $a_n, b_n$, in the sense of `IsLevelPairingValue`. Then $e\,b\,a = -\,e\,a\,b$ for all $a, b \in T_\ell$, and $e\,a\,a = 0$ for all $a \in T_\ell$.
--
--   This is the classical assertion that the Riemann form attached to an invertible sheaf on an abelian variety is alternating, the vanishing on the diagonal being obtained from skew-symmetry because $\mathbb{Z}_\ell$ is torsion-free, including for $\ell = 2$. It feeds the perfectness statement for Riemann forms and the treatment of alternating forms compatible with the Rosati involution in the study of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_isRiemannForm_swap_eq_neg_and_self_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.isRiemannForm_swap_eq_neg_and_self_eq_zero
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (ζ : ℕ → k) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n)
    (e : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he : IsRiemannForm f L hc 𝓛 ℓ ζ e) :
    (∀ a b : TateModule ℓ (L.AlgPoints hc k), e b a = - e a b) ∧ ∀ a : TateModule ℓ (L.AlgPoints hc k), e a a = 0 := by sorry
