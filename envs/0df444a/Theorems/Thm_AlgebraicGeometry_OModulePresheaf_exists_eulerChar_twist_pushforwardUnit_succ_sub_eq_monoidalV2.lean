-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2
-- name    : AlgebraicGeometry.OModulePresheaf.exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/4710076a-a854-5060-bbe3-8df730feabb0
-- title:
--   Kleiman's twisting step for Euler characteristics
-- statement:
--   Let $k$ be a field and let $\pi : V \to \operatorname{Spec} k$ be a proper morphism of schemes. Let $K$ be an ordered affine cover of $V$: a finite linearly ordered index type together with affine opens $U_i$ whose supremum is $\top$. Let $L$ be a module over the structure sheaf of $V$, assumed locally trivial in the sense that every point of $V$ lies in an open $U$ for which the pullback of $L$ along the inclusion $U \hookrightarrow V$ is isomorphic to the unit sheaf of modules of $U$. Let $Z_0$ be a closed subset of $V$ with nonempty underlying set, and assume that the closed subscheme cut out by the vanishing ideal sheaf data of $Z_0$ is integral. The assertion is that there exist closed subsets $Y_1, Y_2$ of $V$ with $Y_1 < Z_0$ and $Y_2 < Z_0$ strictly, and presheaves of $\mathcal{O}$-modules $G_1, G_2$ over $\pi$ (each assigning to an open $U$ a $k$-module and $\Gamma(V,U)$-module with compatible semilinear restriction maps), such that for $j = 1,2$ the presheaf $G_j$ is coherent ($G_j(U)$ is a finite $\Gamma(V,U)$-module for every affine open $U$), quasi-coherent (for every affine open $U$ and $f \in \Gamma(V,U)$, every section over the basic open $D(f)$ becomes, after multiplication by a power of $f$, a restriction from $U$, and every section over $U$ restricting to $0$ on $D(f)$ is killed by a power of $f$) and supported in $Y_j$ ($G_j(U)$ is a subsingleton whenever the affine open $U$ is disjoint from $Y_j$), and such that for every $n \in \mathbb{N}$
--   $$\chi_K\bigl(\iota_*\mathcal{O}_{Z_0} \otimes L^{\otimes (n+1)}\bigr) - \chi_K\bigl(\iota_*\mathcal{O}_{Z_0} \otimes L^{\otimes n}\bigr) = \chi_K\bigl(G_1 \otimes L^{\otimes (n+1)}\bigr) - \chi_K\bigl(G_2 \otimes L^{\otimes n}\bigr).$$
--   Here $\iota$ is the closed immersion of the subscheme of the vanishing ideal of $Z_0$ and $\iota_*\mathcal{O}_{Z_0}$ is the presheaf $U \mapsto \Gamma(\iota^{-1}U, \mathcal{O})$ with its $\Gamma(V,U)$-action through $\iota$; $F \otimes L^{\otimes m}$ is the presheaf $U \mapsto F(U) \otimes_{\Gamma(V,U)} \Gamma(L^{\otimes m}, U)$, with $L^{\otimes m}$ formed by $L^{\otimes 0} = \mathbf{1}$ and $L^{\otimes (m+1)} = L^{\otimes m} \otimes L$; and $\chi_K(F)$ is the alternating sum $\sum_{i < |K.\iota|} (-1)^i \dim_k$ of the $i$-th Čech cohomology module of $F$ on the cover $K$.
--
--   This is the twisting step in Kleiman's proof of Snapper's theorem that $n \mapsto \chi(F \otimes L^{\otimes n})$ is polynomial: the first difference of $n \mapsto \chi(\mathcal{O}_{Z_0} \otimes L^{\otimes n})$ is expressed through coherent data supported on closed subsets strictly smaller than $Z_0$, so that an induction on the support applies. It is used by [`AlgebraicGeometry.OModulePresheaf.exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_polynomial_forall_eulerChar_twist_tensorPow_eq_monoidalV2).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.OModulePresheaf.exists_eulerChar_twist_pushforwardUnit_succ_sub_eq_monoidalV2
    {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π]
    (K : V.OrderedAffineCover) (L : V.Modules)
    (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (Z₀ : Closeds V) (hZ₀ : (Z₀ : Set V).Nonempty)
    (hint : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme) :
    ∃ (Y₁ Y₂ : Closeds V) (G₁ G₂ : OModulePresheaf π),
      Y₁ < Z₀ ∧ Y₂ < Z₀ ∧
      G₁.IsCoherent ∧ G₁.IsQuasicoherent ∧ G₁.SupportedIn Y₁ ∧
      G₂.IsCoherent ∧ G₂.IsQuasicoherent ∧ G₂.SupportedIn Y₂ ∧
      ∀ n : ℕ,
        ((OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι).twist
              (L.tensorPow (n + 1))).eulerChar K -
          ((OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι).twist
              (L.tensorPow n)).eulerChar K =
        (G₁.twist (L.tensorPow (n + 1))).eulerChar K - (G₂.twist (L.tensorPow n)).eulerChar K := by sorry
