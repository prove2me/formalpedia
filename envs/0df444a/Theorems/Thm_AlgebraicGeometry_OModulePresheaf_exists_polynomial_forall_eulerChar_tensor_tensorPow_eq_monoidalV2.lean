-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_tensor_tensorPow_eq_monoidalV2
-- name    : AlgebraicGeometry.OModulePresheaf.exists_polynomial_forall_eulerChar_tensor_tensorPow_eq_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/5a42801a-f34b-57bf-9067-393ed5be8813
-- title:
--   Snapper polynomiality of χ(M ⊗ L^{⊗ n})
-- statement:
--   Let $k$ be a field and $\pi\colon V \to \operatorname{Spec} k$ a proper morphism of schemes, and let $K$ be an ordered affine cover of $V$, that is, a finite linearly ordered index set $K.\iota$ together with opens $U_i \subseteq V$ that are affine and satisfy $\bigsqcup_i U_i = \top$. Let $M$ be a sheaf of $\mathcal O_V$-modules and let `OModulePresheaf.ofModules` $\pi\, M$ be the presheaf of $k$-modules $U \mapsto \Gamma(M,U)$, with its $\Gamma(V,U)$-action and the $k$-structure coming from $\pi$. Assume: `IsCoherent`, i.e. $\Gamma(M,U)$ is a finite $\Gamma(V,U)$-module for every affine open $U$; `IsQuasicoherent`, i.e. for every affine open $U$ and $f \in \Gamma(V,U)$, every section over $V.\mathrm{basicOpen}\,f$ becomes the restriction of a section over $U$ after multiplication by some power of $f$, and every section over $U$ restricting to $0$ on $V.\mathrm{basicOpen}\,f$ is annihilated by some power of $f$; `SupportedIn` $Y$ for a closed $Y \subseteq V$, i.e. $\Gamma(M,U)$ is a subsingleton for every affine open $U$ with $U \cap Y = \emptyset$; and $\operatorname{topologicalKrullDim} Y \le d$ for a natural number $d$. Let $L$ be a sheaf of $\mathcal O_V$-modules such that every point of $V$ lies in an open $U$ with $L$ pulled back along $U \hookrightarrow V$ isomorphic to the unit sheaf of modules of $U$. Then there is $p \in \mathbb Q[X]$ with $\deg p \le d$ such that for every $n \in \mathbb N$ the integer $\sum_{i < |K.\iota|} (-1)^i \dim_k \check H^i(K, M \otimes L^{\otimes n})$ — where $L^{\otimes n}$ is `tensorPow`, defined by $L^{\otimes 0} = \mathbf 1$ and $L^{\otimes (n+1)} = L^{\otimes n} \otimes L$, and the dimensions are those of the groups `H0` and `HSucc` of the presheaf `ofModules` $\pi\,(M \otimes L^{\otimes n})$ on $K$ — equals $p(n)$ in $\mathbb Q$.
--
--   This is Snapper's polynomiality theorem in the form with one invertible sheaf, with Kleiman's bound on the degree by the dimension of the support, stated for the alternating Čech Euler characteristic attached to a fixed finite affine cover. It feeds the multivariable version and, through the twisting computation on projective space, the polynomiality of Hilbert-type characteristics used further on.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_tensor_tensorPow_eq_monoidalV2.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.exists_polynomial_forall_eulerChar_tensor_tensorPow_eq_monoidalV2
    {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π]
    (K : V.OrderedAffineCover) (M : V.Modules)
    (hc : (OModulePresheaf.ofModules π M).IsCoherent) (hq : (OModulePresheaf.ofModules π M).IsQuasicoherent)
    (Y : TopologicalSpace.Closeds V) (hY : (OModulePresheaf.ofModules π M).SupportedIn Y)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ d)
    (L : V.Modules)
    (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    ∃ p : Polynomial ℚ, p.natDegree ≤ d ∧
      ∀ n : ℕ, ((OModulePresheaf.ofModules π (M ⊗ L.tensorPow n)).eulerChar K : ℚ) = p.eval (n : ℚ) := by sorry
