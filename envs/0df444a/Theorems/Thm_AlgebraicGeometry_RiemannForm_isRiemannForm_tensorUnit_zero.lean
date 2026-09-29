-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_isRiemannForm_tensorUnit_zero
-- name    : AlgebraicGeometry.RiemannForm.isRiemannForm_tensorUnit_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/679d19d7-b6df-52cf-a72e-de5a79d38008
-- title:
--   The zero form is a Riemann form of mathcal O_A
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme (in the bottom universe) and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law on $f$: a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points of $A$ over each $t : T \to \operatorname{Spec} k$, with multiplication, unit, inverse, the group axioms and compatibility with base change along $\psi : T' \to T$ over $\operatorname{Spec} k$. Assume $L$ is commutative (`hc`), and that $f$ satisfies `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law. Let $\ell$ be a prime with $\ell \neq 0$ in $k$, and let $\zeta : \mathbb N \to k$ satisfy that each $\zeta_n$ is a primitive $\ell^n$-th root of unity and $\zeta_{n+1}^{\ell} = \zeta_n$. The conclusion is `IsRiemannForm f L hc (𝟙_ A.Modules) ℓ ζ 0`: for the monoidal unit $\mathcal O_A$ of $A$-modules, the zero $\mathbb Z_\ell$-bilinear form on the Tate module $T_\ell$ of the group $L.\mathrm{AlgPoints}\ hc\ k$ of $k$-points (sequences $(x_n)$ with $\ell^n x_n = 0$ and $\ell x_{n+1} = x_n$) satisfies, for all $n$ and all $a, b \in T_\ell$, the relation `IsLevelPairingValue` at level $\ell^n$ for the points $a_n$, $b_n$ and the scalar $\zeta_n^{(0\,a\,b).\mathrm{appr}\,n}$: translation by $a_n$ followed by $[\ell^n]$ equals $[\ell^n]$, and there is an isomorphism $\beta : [\ell^n]^{*}T_{b_n}^{*}\mathcal O_A \cong [\ell^n]^{*}\mathcal O_A$ whose transported conjugate is multiplication by that constant scalar.
--
--   This is the normalisation statement for the Riemann form attached to a line bundle on an abelian scheme with a commutative relative group law: the trivial bundle $\mathcal O_A$ has zero Riemann form, in the sense of the level-$\ell^n$ pairing computed through translations and multiplication by $\ell^n$. It is used in the construction of the $\ell$-adic pairings on fake elliptic curves, where a tensor-unit case has to be identified before Rosati-compatibility arguments can be made.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_isRiemannForm_tensorUnit_zero.lean

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

theorem AlgebraicGeometry.RiemannForm.isRiemannForm_tensorUnit_zero
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (ζ : ℕ → k) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n) :
    IsRiemannForm f L hc (𝟙_ A.Modules) ℓ ζ 0 := by sorry
