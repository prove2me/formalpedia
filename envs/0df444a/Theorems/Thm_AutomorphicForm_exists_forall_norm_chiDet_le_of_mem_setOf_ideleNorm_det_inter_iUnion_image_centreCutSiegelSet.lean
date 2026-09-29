-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_chiDet_le_of_mem_setOf_ideleNorm_det_inter_iUnion_image_centreCutSiegelSet
-- name    : AutomorphicForm.exists_forall_norm_chiDet_le_of_mem_setOf_ideleNorm_det_inter_iUnion_image_centreCutSiegelSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/30ed97a8-78c3-579b-9ae7-0bd39e9ebda5
-- title:
--   Boundedness of χ∘det on a determinant slab in Siegel sets
-- statement:
--   Let $L$ be a number field, and let $\chi$ be a homomorphism from the unit group of the adele ring $\mathbb{A}_L$ of $L$ to $\mathbb{C}^\times$ whose associated $\mathbb{C}$-valued function $z \mapsto \chi(z)$ is continuous (no unitarity is assumed). Let $\alpha, \beta$ be real numbers with $\alpha > 0$, let $c, u, d_1, d_2$ be arbitrary real numbers, and let $T_c$ be a compact subset of $\mathrm{GL}_2(\mathbb{A}_L)$. The assertion is that there is a real number $M$ bounding $|\chi(\det x)|$ for every $x$ lying in the intersection of the determinant slab $\{g : \mathrm{ideleNorm}_L(\det g) \in [\alpha,\beta]\}$, where $\mathrm{ideleNorm}_L$ is the value of the distributive Haar character of $\mathbb{A}_L$ at the given idele, read as a real number, with the union over $y \in T_c$ of the right translates $\mathfrak{S}y$ of the centre-cut Siegel set $\mathfrak{S} = \mathrm{centreCutSiegelSet}\,L\,c\,u\,d_1\,d_2$, that is, the set of $g \in \mathrm{GL}_2(\mathbb{A}_L)$ whose finite component lies in the subgroup `finiteIntegralGL2` of $\mathrm{GL}_2$ of the finite adeles and which satisfy, at every infinite place $w$ of $L$, the height bound $c \le \lVert\det g_w\rVert / \mathrm{rowNormSq}(g_w)$, the window bound $\mathrm{xWindowSq}(g_w) \le u^2$, and $\lVert \det g_w \rVert \in [d_1,d_2]$.
--
--   This is the boundedness of a continuous (not necessarily unitary) idele class quasi-character composed with the determinant on the part of a finite union of translates of a centre-cut Siegel set on which the idele norm of the determinant is confined to a compact interval of positive reals; such estimates go back to the reduction theory of adele groups. It feeds the integrability and limit statement for set integrals of the twisted convolution operator applied to $\chi \circ \det$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_chiDet_le_of_mem_setOf_ideleNorm_det_inter_iUnion_image_centreCutSiegelSet.lean

import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_forall_norm_chiDet_le_of_mem_setOf_ideleNorm_det_inter_iUnion_image_centreCutSiegelSet
    (L : Type) [Field L] [NumberField L]
    (χ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ)
    (hχ : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((χ z : ℂˣ) : ℂ))
    (α β : ℝ) (hα : 0 < α) (c u d₁ d₂ : ℝ)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) :
    ∃ M : ℝ, ∀ x ∈ {g : AdelicGL2 (𝓞 L) L |
        NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β} ∩
          ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂,
      ‖chiDet (𝓞 L) L χ x‖ ≤ M := by sorry
