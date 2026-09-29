-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_tensorProduct_sections_linearEquiv_sections_box_natural_of_isInvertible
-- name    : AlgebraicGeometry.OModulePresheaf.exists_tensorProduct_sections_linearEquiv_sections_box_natural_of_isInvertible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/8366bdc1-ff2f-53dc-9b94-e999b1210189
-- title:
--   Affine Künneth for invertible modules, natural in boxes
-- statement:
--   Let $k$ be a field, let $X$ and $Y$ be schemes, and let $\pi_X\colon X\to\operatorname{Spec} k$ and $\pi_Y\colon Y\to\operatorname{Spec} k$ be separated morphisms. Let $F$ be a module on $X$ and $G$ a module on $Y$, each invertible in the sense of `Scheme.Modules.IsInvertible`: every point of the base has an open neighbourhood $W$ such that the pullback of the module along the inclusion $W\hookrightarrow$ base is isomorphic to the unit sheaf of modules on $W$. Write $P$ for the fibre product of $\pi_X$ and $\pi_Y$, with projections $p_1=$ `pullback.fst` and $p_2=$ `pullback.snd`, structure morphism $p_1$ followed by $\pi_X$, and put $N=p_1^{*}F\otimes p_2^{*}G$ on $P$. The assertion is the existence of a family of $k$-linear isomorphisms $$e_{U,V}\colon \Gamma(F,U)\otimes_k\Gamma(G,V)\;\xrightarrow{\ \sim\ }\;\Gamma\bigl(N,\;p_1^{-1}U\cap p_2^{-1}V\bigr),$$ one for each pair of affine opens $U\subseteq X$, $V\subseteq Y$, where all section modules carry the $k$-structures of `OModulePresheaf.ofModules`, namely scalar restriction along the $k$-algebra structure on $\Gamma(\mathcal O,U)$ coming from the structure morphism, such that the family is compatible with restriction on boxes: for affine opens $U'\le U$ and $V'\le V$ and sections $s\in\Gamma(F,U)$, $t\in\Gamma(G,V)$, the restriction of $e_{U,V}(s\otimes t)$ along $p_1^{-1}U'\cap p_2^{-1}V'\le p_1^{-1}U\cap p_2^{-1}V$ equals $e_{U',V'}(s|_{U'}\otimes t|_{V'})$. The compatibility is asserted on pure tensors.
--
--   This is the affine Künneth statement for a pair of invertible modules: the sections of $p_1^{*}F\otimes p_2^{*}G$ over an affine box $U\times_k V$ are the $k$-tensor product of the sections of $F$ over $U$ and of $G$ over $V$, naturally in the box. It provides the term-by-term identification used to compare the bi-Čech complex of strips on $X\times_k Y$ with the tensor product of the Čech complexes of $F$ and $G$, and is cited by [`AlgebraicGeometry.OModulePresheaf.nonempty_HTot_biCech_strips_equiv_HTot_tensor_ofCech`](thm.html#AlgebraicGeometry.OModulePresheaf.nonempty_HTot_biCech_strips_equiv_HTot_tensor_ofCech).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_tensorProduct_sections_linearEquiv_sections_box_natural_of_isInvertible.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.exists_tensorProduct_sections_linearEquiv_sections_box_natural_of_isInvertible
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of k)) (πY : Y ⟶ Spec (CommRingCat.of k)) [IsSeparated πX] [IsSeparated πY]
    (F : X.Modules) (hF : Scheme.Modules.IsInvertible F)
    (G : Y.Modules) (hG : Scheme.Modules.IsInvertible G) :
    ∃ e : ∀ (U : X.affineOpens) (V : Y.affineOpens),
        (OModulePresheaf.ofModules πX F).obj U.1 ⊗[k] (OModulePresheaf.ofModules πY G).obj V.1 ≃ₗ[k]
          (OModulePresheaf.ofModules (pullback.fst πX πY ≫ πX)
            ((Scheme.Modules.pullback (pullback.fst πX πY)).obj F ⊗
              (Scheme.Modules.pullback (pullback.snd πX πY)).obj G)).obj
            (pullback.fst πX πY ⁻¹ᵁ U.1 ⊓ pullback.snd πX πY ⁻¹ᵁ V.1),
      ∀ (U U' : X.affineOpens) (V V' : Y.affineOpens) (hU : U'.1 ≤ U.1) (hV : V'.1 ≤ V.1)
        (s : (OModulePresheaf.ofModules πX F).obj U.1) (t : (OModulePresheaf.ofModules πY G).obj V.1),
        (OModulePresheaf.ofModules (pullback.fst πX πY ≫ πX)
            ((Scheme.Modules.pullback (pullback.fst πX πY)).obj F ⊗
              (Scheme.Modules.pullback (pullback.snd πX πY)).obj G)).res
          (inf_le_inf ((pullback.fst πX πY).preimage_mono hU) ((pullback.snd πX πY).preimage_mono hV))
          (e U V (s ⊗ₜ t)) =
        e U' V' ((OModulePresheaf.ofModules πX F).res hU s ⊗ₜ (OModulePresheaf.ofModules πY G).res hV t) := by sorry
