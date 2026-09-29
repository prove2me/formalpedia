-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_exists_isFrameOn_isUnit_germToFunctionField_eq_mul_pow_of_tensorPow_iso
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_exists_isFrameOn_isUnit_germToFunctionField_eq_mul_pow_of_tensorPow_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/4a7f93c6-25bc-5d7d-9ac2-22f4b463e486
-- title:
--   Trivialised n-th tensor power: local n-th powers up to one rational function
-- statement:
--   Let $X$ be an integral scheme (over universe $u$), and let $L$ be an $\mathcal O_X$-module object of `X.Modules` that is invertible in the sense of `Scheme.Modules.IsInvertible`: every point of $X$ has an open neighbourhood $U$ for which the pullback of $L$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit sheaf of modules on $U$. Let $n \in \mathbb N$ and suppose given an isomorphism $eL$ in `X.Modules` from `L.tensorPow n` — the iterated tensor product defined by $\mathbb 1$ for $n = 0$ and $L^{\otimes k} \otimes L$ for $n = k+1$ — to the monoidal unit $\mathbb 1$. Let $\varphi$ assign to each open $U \subseteq X$ an additive homomorphism $\varphi_U \colon \Gamma(L,U) \to K(X)$ into the function field of $X$, subject to: compatibility with restriction, $\varphi_V(m|_V) = \varphi_U(m)$ whenever $V \le U$ with $V$ non-empty; semilinearity, $\varphi_U(a \cdot m) = \mathrm{alg}(a)\,\varphi_U(m)$ for $a \in \Gamma(X,U)$ and $m \in \Gamma(L,U)$ with $U$ non-empty, where $\mathrm{alg}$ is the structure map $\Gamma(X,U) \to K(X)$; and injectivity of $\varphi_U$ for every non-empty $U$. The conclusion asserts the existence of a non-zero $F \in K(X)$ such that for every point $x \in X$ there are an open $U$ with $x \in U$, a section $e \in \Gamma(L,U)$ and a section $u \in \Gamma(X,U)$ such that $e$ is a frame on $U$, i.e. for every open $W \le U$ the map $g \mapsto g \cdot (e|_W)$ is a bijection $\Gamma(X,W) \to \Gamma(L,W)$; $u$ is a unit of $\Gamma(X,U)$; and the germ of $u$ at the generic point, $X.germToFunctionField\ U\ u$ (formed using the non-emptiness of $U$ witnessed by $x$), equals $F \cdot \varphi_U(e)^n$.
--
--   This is the function-field form of the statement that an invertible sheaf on an integral scheme with trivialised $n$-th tensor power is locally an $n$-th power up to a single global rational function, the comparison constant $F$ being independent of the point and of the chosen local frame; it is the analogue, inside the constant sheaf $K(X)$, of the classical description of invertible sheaves on integral schemes as Cartier divisors. It is used in the analysis of Néron-model objects attached to modular curves at a place, where a torsion line bundle must be compared place by place with an $n$-th power.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_exists_isFrameOn_isUnit_germToFunctionField_eq_mul_pow_of_tensorPow_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_exists_isFrameOn_isUnit_germToFunctionField_eq_mul_pow_of_tensorPow_iso
    {X : Scheme.{u}} [IsIntegral X]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (n : ℕ)
    (eL : L.tensorPow n ≅ 𝟙_ X.Modules)
    (φ : ∀ U : X.Opens, Γ(L, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ(L, U), φ V (L.presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(L, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) :
    ∃ F : X.functionField, F ≠ 0 ∧ ∀ x : X, ∃ (U : X.Opens) (hx : x ∈ U) (e : Γ(L, U)) (u : Γ(X, U)),
      Scheme.Modules.IsFrameOn e U ∧ IsUnit u ∧
      (letI : Nonempty U := ⟨⟨x, hx⟩⟩; X.germToFunctionField U u) = F * (φ U e) ^ n := by sorry
