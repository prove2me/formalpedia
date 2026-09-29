-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_map_tensorSections_eq_mul_smul_of_map_eq_smul
-- name    : AlgebraicGeometry.Scheme.Modules.map_tensorSections_eq_mul_smul_of_map_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/6c203b4b-d065-50e5-8936-e4f309e47a65
-- title:
--   Transition sections multiply under tensor product
-- statement:
--   Let $X$ be a scheme and let $L$, $L'$ be objects of $X.\mathrm{Modules}$, i.e. sheaves of modules over the structure sheaf of $X$, and let $U, V$ be open subsets of $X$. Given sections $s_U \in \Gamma(L,U)$, $s_V \in \Gamma(L,V)$, $s'_U \in \Gamma(L',U)$, $s'_V \in \Gamma(L',V)$ and ring sections $t, t' \in \Gamma(X, U \sqcap V)$, assume that the restriction of $s_U$ along $U \sqcap V \le U$ equals $t$ times the restriction of $s_V$ along $U \sqcap V \le V$, and likewise that the restriction of $s'_U$ equals $t'$ times the restriction of $s'_V$, both restrictions being taken in the respective presheaves of modules. The conclusion is the corresponding identity for the tensor product $L \otimes L'$ in the monoidal structure on $X.\mathrm{Modules}$: the restriction to $U \sqcap V$ of $\mathrm{tensorSections}\,s_U\,s'_U$ equals $(t t')$ times the restriction to $U \sqcap V$ of $\mathrm{tensorSections}\,s_V\,s'_V$. Here `Scheme.Modules.tensorSections s s'` denotes the section of $L \otimes L'$ over an open $W$ obtained by applying, at $W$, the morphism `tensorSectionsHom` — the unit of the sheafification adjunction on presheaves of modules followed by the comparison isomorphism between the sheafified presheaf tensor product and $L \otimes L'$ — to the elementary tensor $s \otimes_{\Gamma(X,W)} s'$.
--
--   This is the multiplicativity of transition (cocycle) data under tensor product: if two modules are related on an overlap by multiplication by units $t$ and $t'$, their tensor product is related by $t t'$, which is the statement that the Čech description of line bundles turns tensor product into the product of cocycles. It is used in the construction of frames for tensor products of invertible modules, notably by [`AlgebraicGeometry.Scheme.IdealSheafData.exists_isFrameOn_invModule_tensor_module_of_ideal_eq_span`](thm.html#AlgebraicGeometry.Scheme.IdealSheafData.exists_isFrameOn_invModule_tensor_module_of_ideal_eq_span).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_map_tensorSections_eq_mul_smul_of_map_eq_smul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory Opposite AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.map_tensorSections_eq_mul_smul_of_map_eq_smul
    {X : Scheme.{u}} {L L' : X.Modules} {U V : X.Opens}
    (sU : Γ(L, U)) (sV : Γ(L, V)) (sU' : Γ(L', U)) (sV' : Γ(L', V)) (t t' : Γ(X, U ⊓ V))
    (ht : L.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op sU =
      t • L.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op sV)
    (ht' : L'.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op sU' =
      t' • L'.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op sV') :
    (L ⊗ L').presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op (Scheme.Modules.tensorSections sU sU') =
      (t * t') • (L ⊗ L').presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op
        (Scheme.Modules.tensorSections sV sV') := by sorry
