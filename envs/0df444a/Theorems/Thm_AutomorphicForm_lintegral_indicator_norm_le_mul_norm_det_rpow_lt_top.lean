-- Prove2me | Theorems.Thm_AutomorphicForm_lintegral_indicator_norm_le_mul_norm_det_rpow_lt_top
-- name    : AutomorphicForm.lintegral_indicator_norm_le_mul_norm_det_rpow_lt_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/f6b57da5-10b0-5d25-af2c-800bb3297118
-- title:
--   Finiteness of |det|^t over norm balls in GL₂(ℚₚ)
-- statement:
--   Let $p$ be a nonzero prime ideal of the ring of integers of $\mathbb{Q}$, i.e. a point of the height-one spectrum, and write $\mathbb{Q}_p =$ the $p$-adic completion of $\mathbb{Q}$ at $p$, with its norm. Let $B$ and $t$ be real numbers with $1 < t$. The group $\mathrm{GL}_2(\mathbb{Q}_p)$ is equipped with the measurable structure `localGLBorel`, namely the Borel $\sigma$-algebra of its topology, which makes it a Borel space. The assertion is that for every measure $\nu$ on $\mathrm{GL}_2(\mathbb{Q}_p)$ that is a Haar measure, the lower Lebesgue integral with respect to $\nu$ of the function sending $h$ to the product of the $\mathrm{ENNReal}$-valued indicator at $h$ of the set $\{h : \lVert h_{ij}\rVert \le B \text{ for all } i, j \in \{0,1\}\}$ (the entries being those of the underlying $2\times 2$ matrix of $h$) with $\mathrm{ofReal}(\lVert \det h\rVert^{t})$, where $\det h$ is taken as a unit of $\mathbb{Q}_p$ and then coerced into $\mathbb{Q}_p$, is strictly less than $\top$. In words: $\int_{\{\max_{i,j}\lvert h_{ij}\rvert \le B\}} \lvert \det h\rvert^{t}\, d\nu(h) < \infty$. The bound $B$ is an arbitrary real number, no positivity being assumed.
--
--   This is the convergence statement underlying the local Godement–Jacquet integral attached to the characteristic function of a lattice in $M_2(\mathbb{Q}_p)$: the exponent condition $t>1$ is exactly what makes the integral of $\lvert\det\rvert^{t}$ over a bounded region of matrices finite. It supplies the local integrability input for the Godement-type unfolding of $\mathrm{GL}_2$ Rankin–Selberg zeta integrals, being used in the construction of integrable Godement unfoldings for principal series and in the Whittaker-shifted zeta integral statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_lintegral_indicator_norm_le_mul_norm_det_rpow_lt_top.lean

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

open IsDedekindDomain NumberField AutomorphicForm
open LanglandsTunnell.RankinSelberg
open MeasureTheory LanglandsTunnell.TateLocal NumberField.TateGlobal UnramifiedWhittaker LanglandsTunnell.Converse LanglandsTunnell.CubicInduction

open scoped nonZeroDivisors
open NumberField.AdelicLevel (diagOne)

open scoped Classical

theorem AutomorphicForm.lintegral_indicator_norm_le_mul_norm_det_rpow_lt_top
    (p : HeightOneSpectrum (𝓞 ℚ)) (B t : ℝ) (ht : 1 < t) :
    letI := localGLBorel ℚ p
    haveI := borelSpace_localGLBorel ℚ p
    ∀ (ν : Measure (GL (Fin 2) (p.adicCompletion ℚ))) [ν.IsHaarMeasure],
      ∫⁻ h : GL (Fin 2) (p.adicCompletion ℚ),
          Set.indicator {h : GL (Fin 2) (p.adicCompletion ℚ) | ∀ i j : Fin 2, ‖((h : GL (Fin 2) (p.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) i j‖ ≤ B} (fun _ => (1 : ENNReal)) h *
            ENNReal.ofReal (‖((Matrix.GeneralLinearGroup.det h : (p.adicCompletion ℚ)ˣ) : (p.adicCompletion ℚ))‖ ^ t) ∂ν < ⊤ := by sorry
