-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_rightConv_eq_self_of_mem_inf_levelInvariantSubmodule_inf_archCutSubmodule
-- name    : AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_rightConv_eq_self_of_mem_inf_levelInvariantSubmodule_inf_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/9de3a04c-f0b6-516a-ae7c-71d0343c9d53
-- title:
--   Factorizable test function reproducing a cuspidal vector
-- statement:
--   Fix the number field $\mathbb{Q}$ and the general production pins `productionPinsGeneral ℚ` (the `CarrierPins` datum built from the class-representative Siegel set with parameters $c=1/2$, $u=1$, $d_1=1/2$, $d_2=2$, the level groups $N\mapsto \mathrm{levelOne}(N)\cap \mathrm{GL}_2$ of the finite adeles, the Hecke generators, and the adelic box). Let $\xi$ be a homomorphism from the central subgroup $Z$ of these pins to $\mathbb{C}^{\times}$, and let $V$ be a $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ which is a cuspidal constituent for $\xi$: $V$ is contained in the $K$-finite cusp submodule, is stable under right translation by finite-adelic elements and by the row-isometry subgroups at each infinite place, is stable under right convolution with factorizable test functions that are archimedean bi-finite of some type family, is non-zero, and has no proper non-zero submodule with these stability properties. Let $N\neq 0$ be an ideal of $\mathbb{Z}$, let `tys` be an archimedean type family (for each infinite place $w$ a finite list of representations of the row-isometry subgroup at $w$), and let $\varphi$ lie simultaneously in $V$, in the submodule of functions invariant under right multiplication by the level group $U(N)$ of the pins, and in the archimedean cut $\bigsqcap_w\bigvee_i$ of the type submodules attached to `tys`. Then there is $\alpha:\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ which factorizes as a product of a compactly supported smooth function of the archimedean matrix entries and a compactly supported locally constant function of the finite part, such that $\mathrm{rightConv}(\varphi,\alpha)=\varphi$, i.e. $\int \varphi(gx)\alpha(x)\,dx=\varphi(g)$ for all $g$.
--
--   This is the approximate-identity step for cuspidal constituents: a vector of fixed level and fixed archimedean type inside an irreducible cuspidal piece is reproduced exactly by convolution with a single factorizable test function, so that such vectors may be manipulated through the convolution algebra. It is used in the construction of cuspidal constituents with non-vanishing Whittaker coefficient and prescribed archimedean character on the Langlands–Tunnell side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_rightConv_eq_self_of_mem_inf_levelInvariantSubmodule_inf_archCutSubmodule.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.MellinTransform
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell LanglandsTunnell.Converse
open AutomorphicForm
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace LanglandsTunnell.RealArchParam
open scoped nonZeroDivisors

theorem AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_rightConv_eq_self_of_mem_inf_levelInvariantSubmodule_inf_archCutSubmodule
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V)
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (tys : ArchTypeFamily ℚ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ : φ ∈ V ⊓ CuspidalConstituent.levelInvariantSubmodule ℚ (productionPinsGeneral ℚ) N ⊓ archCutSubmodule ℚ tys) :
    ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ := by sorry
