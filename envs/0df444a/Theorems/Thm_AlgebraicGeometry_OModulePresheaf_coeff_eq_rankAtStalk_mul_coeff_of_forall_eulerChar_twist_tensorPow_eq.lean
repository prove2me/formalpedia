-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq
-- name    : AlgebraicGeometry.OModulePresheaf.coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/99c808ba-8ec4-59b8-9d18-b708234705ae
-- title:
--   Top Snapper coefficient equals generic rank times that of L
-- statement:
--   Let $k$ be a field and $\pi\colon V\to\operatorname{Spec}k$ a proper morphism with $V$ integral. Let $K$ be an ordered affine cover of $V$: a finite linearly ordered index set with affine opens $U_i$ whose supremum is $\top$. Let $L$ be an object of `V.Modules` which is locally trivial, in the sense that every point of $V$ has an open neighbourhood $U$ on which the pullback of $L$ along $U\hookrightarrow V$ is isomorphic to the unit sheaf of modules of $U$. Let $d$ be a natural number with $\operatorname{topologicalKrullDim} V\le d$, and let $q\in\mathbb Q[X]$ satisfy, for every $m$, $q(m)=\sum_i(-1)^i\dim_k\check H^i(K,-)$ (the index $i$ running over $0,\dots,|K.\iota|-1$, with $\dim_k$ the $k$-dimension of the alternating Čech cohomology) applied to the presheaf of $\mathcal O_V$-modules $U\mapsto\Gamma(L^{\otimes m},U)$, where $L^{\otimes m}$ is the $m$-th tensor power of $L$ built from the unit by repeated tensoring on the right. Let $F$ be a presheaf of $\mathcal O_V$-modules in the project's sense (a $k$-module and $\Gamma(V,U)$-module $F(U)$ for each open $U$, with compatible semilinear restriction maps) which is coherent, i.e. $F(U)$ is a finite $\Gamma(V,U)$-module for every affine open $U$, and quasi-coherent, i.e. for every affine open $U$ and every $f\in\Gamma(V,U)$ each section over the basic open of $f$ becomes the restriction of a section over $U$ after multiplication by some power of $f$, and a section over $U$ restricting to zero there is annihilated by some power of $f$. Let $p\in\mathbb Q[X]$ satisfy $p(m)=\chi(K,F\otimes L^{\otimes m})$ for all $m$, where the twist is the presheaf $U\mapsto F(U)\otimes_{\Gamma(V,U)}\Gamma(L^{\otimes m},U)$. Finally let $U_0$ be an affine open of $V$ and $\mathfrak p$ a prime of $\Gamma(V,U_0)$ with $\mathfrak p=(0)$. Then $p$ and $q$ have $d$-th coefficients related by $p_d=\operatorname{rankAtStalk}_{\Gamma(V,U_0)}(F(U_0))(\mathfrak p)\cdot q_d$ in $\mathbb Q$, the rank being that of $F(U_0)$ at the generic point $\mathfrak p$.
--
--   This is Kleiman's formula for the leading behaviour of Snapper polynomials, $(\mathcal L^{d}\cdot\mathcal F)=\operatorname{rk}(\mathcal F)\,(\mathcal L^{d})$, expressed through the $d$-th coefficients of the Euler-characteristic polynomials of $\mathcal F\otimes\mathcal L^{\otimes m}$ and of $\mathcal L^{\otimes m}$ computed by alternating Čech cohomology on a fixed finite affine cover. It feeds the computation of degrees of endomorphisms of Jacobians of curves of good reduction, where it is used to identify the degree of multiplication by $n$ on a relative group law with a power.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq
    {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π] [IsIntegral V]
    (K : V.OrderedAffineCover) (L : V.Modules)
    (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (d : ℕ) (hd : topologicalKrullDim V ≤ d)
    (q : Polynomial ℚ)
    (hq : ∀ m : ℕ, ((OModulePresheaf.ofModules π (L.tensorPow m)).eulerChar K : ℚ) = q.eval (m : ℚ))
    (F : OModulePresheaf π) (hc : F.IsCoherent) (hqc : F.IsQuasicoherent)
    (p : Polynomial ℚ)
    (hp : ∀ m : ℕ, ((F.twist (L.tensorPow m)).eulerChar K : ℚ) = p.eval (m : ℚ))
    (U₀ : V.affineOpens) (𝔭 : PrimeSpectrum Γ(V, U₀.1)) (h𝔭 : 𝔭.asIdeal = ⊥) :
    p.coeff d = (Module.rankAtStalk (R := Γ(V, U₀.1)) (F.obj U₀.1) 𝔭 : ℚ) * q.coeff d := by sorry
