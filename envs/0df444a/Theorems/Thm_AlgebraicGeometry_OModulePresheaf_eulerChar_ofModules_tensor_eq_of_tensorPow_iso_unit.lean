-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_ofModules_tensor_eq_of_tensorPow_iso_unit
-- name    : AlgebraicGeometry.OModulePresheaf.eulerChar_ofModules_tensor_eq_of_tensorPow_iso_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/572e72e4-3824-561c-b443-c311bbe2b3f3
-- title:
--   Twisting by a torsion line bundle preserves the Euler characteristic
-- statement:
--   Let $k$ be a field, $V$ a scheme and $\pi\colon V\to\operatorname{Spec} k$ a proper morphism; let $K$ be an ordered affine cover of $V$, that is, a finite linearly ordered index type $\iota$ together with affine opens $U_i\subseteq V$ whose supremum is $\top$. Let $M$ be an $\mathcal O_V$-module, and let `ofModules` $\pi\,M$ be the associated presheaf of $k$-modules $U\mapsto \Gamma(M,U)$ with the $k$-structure coming from $\pi$ and the usual restriction maps. Assume: (i) coherence, i.e. $\Gamma(M,U)$ is a finite $\Gamma(V,U)$-module for every affine open $U$; (ii) quasi-coherence, i.e. for every affine open $U$ and $f\in\Gamma(V,U)$ every section over $V_f$ becomes, after multiplication by some $f^n$, a restriction from $U$, and every section over $U$ restricting to $0$ on $V_f$ is killed by some $f^n$; (iii) that the presheaf is supported in a closed subset $Y\subseteq V$, i.e. $\Gamma(M,U)$ is a subsingleton whenever the affine open $U$ misses $Y$; (iv) $\dim Y\le d$ for a natural number $d$, in the sense of topological Krull dimension. Let $L$ be an $\mathcal O_V$-module that is Zariski-locally trivial: every point of $V$ has an open neighbourhood $U$ for which the pullback of $L$ along $U\hookrightarrow V$ is isomorphic to the unit sheaf of modules on $U$. Assume finally $n>0$ and an isomorphism $L^{\otimes n}\cong\mathbf 1$, where $L^{\otimes 0}=\mathbf 1$ and $L^{\otimes(m+1)}=L^{\otimes m}\otimes L$. Then the Euler characteristics with respect to $K$ agree: the alternating sum $\sum_{i<|\iota|}(-1)^i\dim_k$ of the Čech modules of `ofModules` $\pi\,(M\otimes L)$ equals that of `ofModules` $\pi\,M$.
--
--   This is the standard consequence of Snapper's polynomiality theorem that twisting a coherent sheaf by a torsion line bundle leaves its Euler characteristic unchanged. It is used in the treatment of Euler characteristics on abelian schemes and relative group laws, where it feeds the computation of $\chi$ under pullback by multiplication maps and the stabiliser criterion for non-vanishing $\chi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_ofModules_tensor_eq_of_tensorPow_iso_unit.lean

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

theorem AlgebraicGeometry.OModulePresheaf.eulerChar_ofModules_tensor_eq_of_tensorPow_iso_unit
    {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π]
    (K : V.OrderedAffineCover) (M : V.Modules)
    (hc : (OModulePresheaf.ofModules π M).IsCoherent) (hq : (OModulePresheaf.ofModules π M).IsQuasicoherent)
    (Y : TopologicalSpace.Closeds V) (hY : (OModulePresheaf.ofModules π M).SupportedIn Y)
    (d : ℕ) (hd : topologicalKrullDim Y ≤ d)
    (L : V.Modules)
    (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (n : ℕ) (hn : 0 < n) (e : L.tensorPow n ≅ 𝟙_ V.Modules) :
    (OModulePresheaf.ofModules π (M ⊗ L)).eulerChar K = (OModulePresheaf.ofModules π M).eulerChar K := by sorry
