-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_sum_mul_apply_mul_mem_and_arch_transfer_of_mem_isCuspConstituent_of_mem_finiteAdelicGL2Subgroup
-- name    : AutomorphicForm.CuspidalConstituent.sum_mul_apply_mul_mem_and_arch_transfer_of_mem_isCuspConstituent_of_mem_finiteAdelicGL2Subgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/3fa6116c-a8d7-5438-80fb-ffd7895802b0
-- title:
--   Finite-adelic translates preserve a cuspidal constituent and its archimedean data
-- statement:
--   Work over $\mathbb{Q}$. Let $\xi$ be a homomorphism from the group $Z$ attached to the pins `productionPinsGeneral ℚ` to $\mathbb{C}^\times$, and let $V$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ which is a cuspidal constituent for these data, i.e. $V$ satisfies `IsCuspSubrep`, is non-zero, and every `IsCuspSubrep` submodule $W \le V$ is $\bot$ or $V$. Assume every element of $V$ is `IsArchSmoothAt` every real place $w$, i.e. for each $g$ the function $e \mapsto \varphi(g \cdot \mathrm{archRealLiftAt}\,e)$ is $C^\infty$ on the invertible $2\times 2$ real matrices. Let $\varphi \in V$, $m \in \mathbb{N}$, scalars $c_i \in \mathbb{C}$ and elements $g_i$ lying in `finiteAdelicGL2Subgroup ℚ`, the kernel of the archimedean projection `glArch`. Then $\varphi'(x) = \sum_i c_i \varphi(x g_i)$ again lies in $V$, and inherits from $\varphi$: continuity; membership in $\mathrm{archCutSubmodule}$ of any archimedean type family $\mathrm{tys}$ (the intersection over infinite places of the spans of the listed type submodules); the transformation law `HasArchCharacterAt₀` for the character $\mathrm{archWeightCharAt}\,hw\,n$, the $n$-th power of $\mathrm{archWeightOneAt}\,hw$, for every real $w$ and $n \in \mathbb{Z}$; smoothness together with any Casimir eigenvalue equation $\mathrm{archCasimirAt}\,hw\,\varphi = \lambda\varphi$; any eigenrelation $\varphi(x\,J) = e\,\varphi(x)$ under the real element $J$ at $w$; any relation $\varphi(x\,J) = c_J\,(H - i(E+F))\varphi(x)$, where $H, E, F$ are the derivatives $\mathrm{archDerivAt}$ along the corresponding one-parameter flows; and annihilation by $H - i(E+F)$.
--
--   This is the stability statement that right translation by finite adeles, extended to finite $\mathbb{C}$-linear combinations, acts on a cuspidal constituent and commutes with all archimedean conditions (weight, Casimir eigenvalue, behaviour under $J$, annihilation by the lowering operator). It is used in the construction of a vector in a cuspidal constituent with non-vanishing Whittaker coefficient satisfying the prescribed archimedean and $J$-rigidity relations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_sum_mul_apply_mul_mem_and_arch_transfer_of_mem_isCuspConstituent_of_mem_finiteAdelicGL2Subgroup.lean

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

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace LanglandsTunnell.RealArchParam
open scoped nonZeroDivisors

theorem AutomorphicForm.CuspidalConstituent.sum_mul_apply_mul_mem_and_arch_transfer_of_mem_isCuspConstituent_of_mem_finiteAdelicGL2Subgroup
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V)
    (hsmV : ∀ (w : InfinitePlace ℚ) (hw : w.IsReal), ∀ x ∈ V, IsArchSmoothAt hw x)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφV : φ ∈ V)
    (m : ℕ) (c : Fin m → ℂ) (g : Fin m → AdelicGL2 (𝓞 ℚ) ℚ) (hg : ∀ i, g i ∈ finiteAdelicGL2Subgroup ℚ) :
    let φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := fun x => ∑ i, c i * φ (x * g i)
    φ' ∈ V ∧
    (Continuous φ → Continuous φ') ∧
    (∀ tys : ArchTypeFamily ℚ, φ ∈ archCutSubmodule ℚ tys → φ' ∈ archCutSubmodule ℚ tys) ∧
    (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (n : ℤ),
      HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ → HasArchCharacterAt₀ ℚ w (archWeightCharAt hw n) φ') ∧
    (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (lam : ℂ),
      (IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = lam • φ) →
        (IsArchSmoothAt hw φ' ∧ archCasimirAt hw φ' = lam • φ')) ∧
    (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (e : ℂ),
      (∀ x : AdelicGL2 (𝓞 ℚ) ℚ, φ (x * archRealGLAt hw UpperHalfPlane.J) = e * φ x) →
        ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, φ' (x * archRealGLAt hw UpperHalfPlane.J) = e * φ' x) ∧
    (∀ (w : InfinitePlace ℚ) (hw : w.IsReal) (cJ : ℂ),
      (∀ x : AdelicGL2 (𝓞 ℚ) ℚ, φ (x * archRealGLAt hw UpperHalfPlane.J) = cJ * (archDerivAt hw ArchDir.H φ - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ)) x) →
        ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, φ' (x * archRealGLAt hw UpperHalfPlane.J) = cJ * (archDerivAt hw ArchDir.H φ' - Complex.I • (archDerivAt hw ArchDir.E φ' + archDerivAt hw ArchDir.Fm φ')) x) ∧
    (∀ (w : InfinitePlace ℚ) (hw : w.IsReal), (archDerivAt hw ArchDir.H φ - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ)) = 0 → (archDerivAt hw ArchDir.H φ' - Complex.I • (archDerivAt hw ArchDir.E φ' + archDerivAt hw ArchDir.Fm φ')) = 0) := by sorry
