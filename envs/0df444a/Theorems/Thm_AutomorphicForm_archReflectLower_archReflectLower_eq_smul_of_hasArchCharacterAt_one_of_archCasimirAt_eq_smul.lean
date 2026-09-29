-- Prove2me | Theorems.Thm_AutomorphicForm_archReflectLower_archReflectLower_eq_smul_of_hasArchCharacterAt_one_of_archCasimirAt_eq_smul
-- name    : AutomorphicForm.archReflectLower_archReflectLower_eq_smul_of_hasArchCharacterAt_one_of_archCasimirAt_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/8082a06a-a0b4-5f14-bba2-bb5f170b57d7
-- title:
--   Square of the J-reflected lowering operator in weight one
-- statement:
--   Let $F$ be a number field, $w$ a real infinite place of $F$ (witnessed by `hw : w.IsReal`), $\lambda \in \mathbb{C}$, and let $x : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a function on the adelic group `AdelicGL2 (𝓞 F) F` which is smooth at $w$ in the sense of `IsArchSmoothAt hw`, i.e. for every $g$ the map $e \mapsto x(g \cdot \iota_w(e))$ is $C^\infty$ on the set of real $2\times 2$ matrices of nonzero determinant, where $\iota_w$ places a real matrix in the factor at $w$; which satisfies the predicate `HasArchCharacterAt₀ F w (archWeightCharAt hw 1) x`, expressing that $x$ transforms at $w$ under the first power of the weight-one character `archWeightOneAt hw` of the row-isometry subgroup of $GL_2(F_w)$; and which is an eigenvector, with eigenvalue $\lambda$, of the Casimir operator at $w$, $\mathrm{archCasimirAt} = -\bigl(\tfrac14 D_H D_H - \tfrac12 D_H + D_E D_{F^-}\bigr)$, where $D_d$ is the derivative at $t=0$ of right translation along the one-parameter flow `archFlowAt hw d t` at $w$. Put $L := D_H - i(D_E + D_{F^-})$ and $(Ty)(g) := (Ly)(g\,J_w)$, with $J_w$ the image under `archRealGLAt hw` of `UpperHalfPlane.J`. The conclusion is twofold: first $T(Tx) = (1-4\lambda)\,x$; second, for every $\kappa \in \mathbb{C}$ with $\kappa^2(1-4\lambda) = 1$ and every $g$, $(x + \kappa\,Tx)(g\,J_w) = \kappa\,\bigl(L(x + \kappa\,Tx)\bigr)(g)$.
--
--   This is the $(\mathfrak{g},K)$-computation for $GL_2(\mathbb{R})$ in which conjugation by $J$ exchanges the lowering and raising operators, so that on a weight-one Casimir eigenvector the composite acts by the scalar $1-4\lambda$; the second clause produces, for each square root $\kappa$ of $(1-4\lambda)^{-1}$, a combination $x + \kappa\,Tx$ whose value at $g J$ is $\kappa$ times the lowering derivative at $g$. It is used in the construction of the weight-one automorphic form with prescribed archimedean behaviour in the converse direction of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archReflectLower_archReflectLower_eq_smul_of_hasArchCharacterAt_one_of_archCasimirAt_eq_smul.lean

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

theorem AutomorphicForm.archReflectLower_archReflectLower_eq_smul_of_hasArchCharacterAt_one_of_archCasimirAt_eq_smul
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal) (lam : ℂ)
    (x : AdelicGL2 (𝓞 F) F → ℂ)
    (_hsm : IsArchSmoothAt hw x)
    (_hwt : HasArchCharacterAt₀ F w (archWeightCharAt hw 1) x)
    (_hcas : archCasimirAt hw x = lam • x) :
    let T : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) := fun y g =>
      (archDerivAt hw ArchDir.H y - Complex.I • (archDerivAt hw ArchDir.E y + archDerivAt hw ArchDir.Fm y))
        (g * archRealGLAt hw UpperHalfPlane.J)
    T (T x) = (1 - 4 * lam) • x ∧

    ∀ κ : ℂ, κ ^ 2 * (1 - 4 * lam) = 1 →
      ∀ g : AdelicGL2 (𝓞 F) F,
        (x + κ • T x) (g * archRealGLAt hw UpperHalfPlane.J)
          = κ * (archDerivAt hw ArchDir.H (x + κ • T x)
                  - Complex.I • (archDerivAt hw ArchDir.E (x + κ • T x) + archDerivAt hw ArchDir.Fm (x + κ • T x))) g := by sorry
