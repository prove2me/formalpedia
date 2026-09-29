-- Prove2me | Theorems.Thm_AutomorphicForm_WhittakerModel_norm_diagUnits2_mul_le_of_forall_mem_localLevelOne_norm_diagUnits2_mul_le
-- name    : AutomorphicForm.WhittakerModel.norm_diagUnits2_mul_le_of_forall_mem_localLevelOne_norm_diagUnits2_mul_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/296dcddc-9bef-5829-8b10-c45e60d3c9d5
-- title:
--   Propagating a Whittaker gauge from the level-one subgroup to GL₂
-- statement:
--   Fix a height-one prime $p$ of the ring of integers of $\mathbb{Q}$ and write $F$ for the completion `p.adicCompletion ℚ` with its absolute value $\|\cdot\|$. Let $w : GL_2(F) \to \mathbb{C}$ satisfy $\|w(n(x)g)\| = \|w(g)\|$ for all $x \in F$ and $g \in GL_2(F)$, where $n(x)$ is `unipotent x`, the matrix $\begin{pmatrix}1&x\\0&1\end{pmatrix}$. Let $C, \tau \in \mathbb{R}$ with $C \ge 0$ and let $A$ be a natural number. Assume the gauge bound $\|w(\mathrm{diag}(a_1,a_2)\,k)\| \le C\,\|a_2\|^{\tau}\,\max\bigl(1, (\|a_1a_2^{-1}\|^{A})^{-1}\bigr)$ for all units $a_1, a_2 \in F^{\times}$ and all $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the subgroup of $GL_2(F)$ consisting of those elements whose image under `localEmbed` (placement at the place $p$, identity entries elsewhere) lies in `finiteLevelOne` for the ideal $\top$, i.e. satisfies `IsLevelOneMatrix` both for the matrix and for its inverse; here $\mathrm{diag}(a_1,a_2)$ is `diagUnits2 a₁ a₂`. The conclusion is that for every $g_0 \in GL_2(F)$ and all units $a_1, a_2$, writing $r(g_0) = \max(\|(g_0)_{10}\|, \|(g_0)_{11}\|)$ for the maximum of the absolute values of the two entries of the bottom row of $g_0$, $$\|w(\mathrm{diag}(a_1,a_2)\,g_0)\| \le C\,\|a_2\|^{\tau}\,r(g_0)^{\tau}\,\max\bigl(1,(\|a_1a_2^{-1}\|^{A})^{-1}\bigr)\,\max\Bigl(1,\bigl((\|\det g_0\|/r(g_0)^2)^{A}\bigr)^{-1}\Bigr).$$
--
--   This is the elementary translation step in the convergence argument for local Rankin–Selberg integrals: a majorant for $|w|$ on the torus times the level-one subgroup is transported, via the Iwasawa decomposition of $g_0$, to the torus times an arbitrary $g_0$, at the cost of explicit factors depending only on $|\det g_0|$ and on the size of the bottom row of $g_0$. It is used in the estimates `exists_forall_lintegral_enorm_jacquetIntegral_mul_whittaker_mul_translate_mul_row_le_of_admissible_of_chamber` and `forall_exists_integrable_godementZeta2_whittaker_shift`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WhittakerModel_norm_diagUnits2_mul_le_of_forall_mem_localLevelOne_norm_diagUnits2_mul_le.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_CellBumps
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_LambdaSquared
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_Congruence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell.RankinSelberg MeasureTheory
  LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker
  LanglandsTunnell.Converse LanglandsTunnell.CubicInduction
open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem AutomorphicForm.WhittakerModel.norm_diagUnits2_mul_le_of_forall_mem_localLevelOne_norm_diagUnits2_mul_le
    (p : HeightOneSpectrum (𝓞 ℚ))
    (w : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hwN : ∀ (x : (p.adicCompletion ℚ)) (g : GL (Fin 2) (p.adicCompletion ℚ)), ‖w (unipotent x * g)‖ = ‖w g‖)
    (C τ : ℝ) (A : ℕ) (hC : 0 ≤ C)
    (hgauge : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ a₁ a₂ : (p.adicCompletion ℚ)ˣ,
      ‖w (diagUnits2 a₁ a₂ * k)‖ ≤
        C * ‖((a₂ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ ^ τ * max 1 ((‖((a₁ * a₂⁻¹ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ ^ A)⁻¹)) :
    ∀ (g₀ : GL (Fin 2) (p.adicCompletion ℚ)) (a₁ a₂ : (p.adicCompletion ℚ)ˣ),
      ‖w (diagUnits2 a₁ a₂ * g₀)‖ ≤
        C * ‖((a₂ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ ^ τ * (max ‖((g₀ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖ ‖((g₀ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖) ^ τ *
          max 1 ((‖((a₁ * a₂⁻¹ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ ^ A)⁻¹) *
          max 1 (((‖((Matrix.GeneralLinearGroup.det g₀ : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ / (max ‖((g₀ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0‖ ‖((g₀ : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1‖) ^ 2) ^ A)⁻¹) := by sorry
