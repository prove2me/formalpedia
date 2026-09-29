-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq
-- name    : AlgebraicGeometry.OModulePresheaf.exists_eulerChar_twist_pushforwardUnit_succ_sub_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/4d72e0c9-f481-53ac-b8d6-aa4d4af7b198
-- title:
--   Kleiman's twisting step for Euler characteristics
-- statement:
--   Let $k$ be a field, $V$ a scheme and $\pi : V \to \operatorname{Spec} k$ a proper morphism, and let $K$ be an ordered affine cover of $V$, that is, a finite linearly ordered index type $\iota$ together with affine opens $U_i$ whose supremum is $\top$. Let $L$ be an $\mathcal{O}_V$-module such that every point of $V$ lies in an open $U$ for which the pullback of $L$ along the inclusion $U \to V$ is isomorphic to the unit module sheaf on $U$. Let $Z_0$ be a closed subset of $V$ whose underlying set is nonempty, and assume that the closed subscheme cut out by the vanishing ideal sheaf data of $Z_0$ is integral. Then there are closed subsets $Y_1, Y_2$ with $Y_1 < Z_0$ and $Y_2 < Z_0$ in the lattice of closed subsets, and presheaves $G_1, G_2$ of $\mathcal{O}_V$-modules over $\pi$ (each assigning to an open $U$ a $\Gamma(V,U)$-module and an $R$-module compatibly, with restriction maps), such that each $G_j$ is coherent (finite $\Gamma(V,U)$-module on every affine open $U$), quasi-coherent (on every affine open $U$ and $f \in \Gamma(V,U)$, every section over $V_f$ becomes a restriction after multiplication by a power of $f$, and every section over $U$ restricting to $0$ on $V_f$ is killed by a power of $f$), and supported in $Y_j$ (the module over an affine open disjoint from $Y_j$ is trivial), and such that for every $n \in \mathbb{N}$, writing $F \mapsto F$ twisted by $M$ for the presheaf $U \mapsto F(U) \otimes_{\Gamma(V,U)} \Gamma(M,U)$, $L^{\otimes 0}$ the unit and $L^{\otimes(n+1)} = L^{\otimes n} \otimes L$, $P$ the presheaf $U \mapsto \Gamma(\iota^{-1}U, \mathcal{O})$ for the closed immersion $\iota$ of that subscheme, and $\chi_K$ for the alternating sum $\sum_{i < \#\iota} (-1)^i \dim_k$ of the ordered Čech cohomology of $K$, one has $\chi_K(P \otimes L^{\otimes(n+1)}) - \chi_K(P \otimes L^{\otimes n}) = \chi_K(G_1 \otimes L^{\otimes(n+1)}) - \chi_K(G_2 \otimes L^{\otimes n})$.
--
--   This is the twisting step in Kleiman's proof of Snapper's theorem: the first difference of $n \mapsto \chi(\mathcal{O}_{Z_0} \otimes L^{\otimes n})$ is expressed through coherent data supported on closed subsets strictly smaller than $Z_0$, so that an induction on dimension applies. It is used in the proof that $n \mapsto \chi(F \otimes L^{\otimes n})$ agrees with a polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_eulerChar_twist_pushforwardUnit_succ_sub_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.OModulePresheaf.exists_eulerChar_twist_pushforwardUnit_succ_sub_eq
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
