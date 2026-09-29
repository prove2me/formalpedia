-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_map_tensorPowAdd_hom_comp_pullbackTensorPowIso_tensorPowMapIso_hom
-- name    : AlgebraicGeometry.Scheme.Modules.map_tensorPowAdd_hom_comp_pullbackTensorPowIso_tensorPowMapIso_hom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/794b042c-043c-5f8a-8444-355d561f4b87
-- title:
--   Pullback compatibility of tensor-power multiplication isomorphisms
-- statement:
--   Let $c : X' \to X$ be a morphism of schemes, let $L$ be an $\mathcal O_X$-module and $L'$ an $\mathcal O_{X'}$-module, let $e$ be an isomorphism from the inverse image $(\mathrm{pullback}\ c)(L)$ to $L'$, and let $m, n$ be natural numbers. Here tensor powers are defined recursively by $L^{\otimes 0} = \mathbf 1$ and $L^{\otimes(n+1)} = L^{\otimes n} \otimes L$; `tensorPowAdd L m n`, an isomorphism $L^{\otimes m} \otimes L^{\otimes n} \cong L^{\otimes(m+n)}$, is the right unitor for $n = 0$ and, for $n+1$, the inverse associator followed by right-whiskering of `tensorPowAdd L m n` by $L$; `tensorPowMapIso e n` is the identity for $n = 0$ and `tensorPowMapIso e n` $\otimes\, e$ for $n+1$; `pullbackTensorObjIso` is the inverse of the tensorator $\mu$ of the monoidal functor $\mathrm{pullback}\ c$, `pullbackTensorUnitObjIso` the inverse of its unit comparison, and `pullbackTensorPowIso c L n`, an isomorphism $(\mathrm{pullback}\ c)(L^{\otimes n}) \cong ((\mathrm{pullback}\ c)(L))^{\otimes n}$, is built from these by the same recursion. Writing $\pi_k$ for `pullbackTensorPowIso c L k` followed by `tensorPowMapIso e k`, the assertion is that $(\mathrm{pullback}\ c)(\mathrm{tensorPowAdd}\ L\ m\ n)$ followed by $\pi_{m+n}$ equals `pullbackTensorObjIso` followed by $\pi_m \otimes \pi_n$ followed by `tensorPowAdd L' m n`.
--
--   This is a coherence statement saying that the comparison isomorphisms $c^*(L^{\otimes k}) \cong (L')^{\otimes k}$ are multiplicative for the graded multiplication maps $L^{\otimes m} \otimes L^{\otimes n} \to L^{\otimes(m+n)}$; no hypothesis on $c$, $L$ or $e$ beyond those stated is needed. It is used in the comparison of sections of tensor powers under pullback, feeding the graded algebra $\bigoplus_n \Gamma(L^{\otimes n})$ attached to a line bundle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_map_tensorPowAdd_hom_comp_pullbackTensorPowIso_tensorPowMapIso_hom.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

theorem AlgebraicGeometry.Scheme.Modules.map_tensorPowAdd_hom_comp_pullbackTensorPowIso_tensorPowMapIso_hom
    {X X' : Scheme.{u}} (c : X' ⟶ X) (L : X.Modules) (L' : X'.Modules) (e : (Scheme.Modules.pullback c).obj L ≅ L')
    (m n : ℕ) :
    (Scheme.Modules.pullback c).map (Scheme.Modules.tensorPowAdd L m n).hom ≫
        (Scheme.Modules.pullbackTensorPowIso c L (m + n) ≪≫ Scheme.Modules.tensorPowMapIso e (m + n)).hom =
      (Scheme.Modules.pullbackTensorObjIso c (L.tensorPow m) (L.tensorPow n)).hom ≫
        ((Scheme.Modules.pullbackTensorPowIso c L m ≪≫ Scheme.Modules.tensorPowMapIso e m).hom ⊗ₘ
          (Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom) ≫
        (Scheme.Modules.tensorPowAdd L' m n).hom := by sorry
