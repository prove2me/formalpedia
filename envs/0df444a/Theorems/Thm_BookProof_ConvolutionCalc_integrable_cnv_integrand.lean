-- Prove2me | Theorems.Thm_BookProof_ConvolutionCalc_integrable_cnv_integrand
-- name    : BookProof.ConvolutionCalc.integrable_cnv_integrand
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T09:12:51.01898+00:00
-- url     : https://prove2.me/theorems/a89128cb-d412-4469-9b9d-a78494716410
-- title:
--   `BookProof.ConvolutionCalc.integrable_cnv_integrand` {u g : Vd d → ℂ} (hu : LocallyIntegrable u (volume : Measure (Vd d))) (hg : Continuous g) (hgc : HasCompactSupport g) (x : Vd d
-- statement:
--   Prove the following Lean 4 theorem from `ChapterConvolutionCalc`.
--
--   `BookProof.ConvolutionCalc.integrable_cnv_integrand` {u g : Vd d → ℂ} (hu : LocallyIntegrable u (volume : Measure (Vd d))) (hg : Continuous g) (hgc : HasCompactSupport g) (x : Vd d) : Integrable (fun y => u y * g (x - y)) (volume : Measure (Vd d))
--
--   Formalization note: Lean 4 identifier `BookProof.ConvolutionCalc.integrable_cnv_integrand`.

-- Generated from ChapterConvolutionCalc.lean — theorem BookProof.ConvolutionCalc.integrable_cnv_integrand
import Definitions.Def_ChapterQgOneParticleCcEsa
import Definitions.Def_ChapterDegSchrodingerCore
import Mathlib
import Definitions.Def_ChapterConvolutionCalc
import Definitions.Def_ChapterHermiteProductCore
open BookProof.HermiteProductCore
open BookProof.ConvolutionCalc



open MeasureTheory
open BookProof.HermiteProductCore BookProof.QgOneParticleCc BookProof.DegSchrodinger

noncomputable section

variable {d : ℕ}

theorem BookProof.ConvolutionCalc.integrable_cnv_integrand {u g : Vd d → ℂ}
    (hu : LocallyIntegrable u (volume : Measure (Vd d))) (hg : Continuous g)
    (hgc : HasCompactSupport g) (x : Vd d) :
    Integrable (fun y => u y * g (x - y)) (volume : Measure (Vd d)) := by sorry
