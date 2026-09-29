-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_tensorPowAdd_tensorSections
-- name    : AlgebraicGeometry.Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_tensorPowAdd_tensorSections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/a9e79c63-a8ff-5f65-9986-2c1786cce866
-- title:
--   Pullback of global sections is multiplicative on tensor powers
-- statement:
--   Let $c : X' \to X$ be a morphism of schemes, $L$ an object of `X.Modules`, $L'$ an object of `X'.Modules`, and $e$ an isomorphism $(\mathrm{pullback}\ c)(L) \cong L'$; let $m, n$ be natural numbers and let $s$ be a section over $\top$ of `L.tensorPow m` and $t$ a section over $\top$ of `L.tensorPow n`, where `tensorPow L 0` is the monoidal unit and `tensorPow L (k+1) = tensorPow L k ⊗ L`. Write $\mathrm{can}_k$ for the map on sections over $\top$ induced by `pullbackTensorPowIso c L k` followed by `tensorPowMapIso e k`, i.e. by the composite $c^*(L^{\otimes k}) \cong (c^*L)^{\otimes k} \cong L'^{\otimes k}$ built recursively from the inverses of the unit and tensor comparison isomorphisms of the monoidal functor $c^*$ and from $e$; write $c^*$ on sections for the effect over $\top$ of the unit of `pullbackPushforwardAdjunction c`; and write `tensorSections` for the section of a tensor product determined by a pair of sections through the sheafification unit. Then applying $\mathrm{can}_{m+n} \circ c^*$ to the image of `tensorSections s t` under `tensorPowAdd L m n` gives the same element as applying `tensorPowAdd L' m n` to `tensorSections` of $\mathrm{can}_m(c^*s)$ and $\mathrm{can}_n(c^*t)$, where `tensorPowAdd` is the isomorphism $L^{\otimes m} \otimes L^{\otimes n} \cong L^{\otimes (m+n)}$ defined by recursion on $n$ from the right unitor and the associator.
--
--   This is the statement that pulling back global sections along $c$ is multiplicative for the graded multiplication on $\bigoplus_k \Gamma(X, L^{\otimes k})$ transported through the canonical comparison isomorphisms $c^*(L^{\otimes k}) \cong L'^{\otimes k}$. It is the multiplicativity input used in [`AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_apply_eq_pullback_of_isPullback`](thm.html#AlgebraicGeometry.GradedOAlgebra.IsSectionRing.exists_algHom_apply_eq_pullback_of_isPullback), where a ring homomorphism between section rings is produced from a pullback square.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_app_pullbackTensorPowIso_tensorPowMapIso_tensorPowAdd_tensorSections.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

theorem AlgebraicGeometry.Scheme.Modules.app_pullbackTensorPowIso_tensorPowMapIso_tensorPowAdd_tensorSections
    {X X' : Scheme.{u}} (c : X' ⟶ X) (L : X.Modules) (L' : X'.Modules) (e : (Scheme.Modules.pullback c).obj L ≅ L')
    (m n : ℕ) (s : Γ(L.tensorPow m, ⊤)) (t : Γ(L.tensorPow n, ⊤)) :
    ((Scheme.Modules.pullbackTensorPowIso c L (m + n) ≪≫ Scheme.Modules.tensorPowMapIso e (m + n)).hom.app ⊤)
        ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow (m + n))).app ⊤)
          (((Scheme.Modules.tensorPowAdd L m n).hom.app ⊤) (Scheme.Modules.tensorSections s t)))
      = ((Scheme.Modules.tensorPowAdd L' m n).hom.app ⊤)
          (Scheme.Modules.tensorSections
            (((Scheme.Modules.pullbackTensorPowIso c L m ≪≫ Scheme.Modules.tensorPowMapIso e m).hom.app ⊤) ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow m)).app ⊤) s))
            (((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤) ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) t))) := by sorry
