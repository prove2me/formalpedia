-- Prove2me | Theorems.Thm_BookProof_FockNumberPreservingGap_number_quadForm_ge
-- name    : BookProof.FockNumberPreservingGap.number_quadForm_ge
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T20:37:49.100976+00:00
-- url     : https://prove2.me/theorems/af6f928d-64f7-4562-8e2f-878fc3de5059
-- title:
--   `BookProof.FockNumberPreservingGap.number_quadForm_ge` {u : FockAlg} (h0 : u 0 = 0) : ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma numberCol u)) : ℂ).re
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockNumberPreservingGap`.
--
--   `BookProof.FockNumberPreservingGap.number_quadForm_ge` {u : FockAlg} (h0 : u 0 = 0) : ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma numberCol u)) : ℂ).re
--
--   Formalization note: Lean 4 identifier `BookProof.FockNumberPreservingGap.number_quadForm_ge`.

-- Generated from ChapterFockNumberPreservingGap.lean — theorem BookProof.FockNumberPreservingGap.number_quadForm_ge
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.FockNumberPreservingGap


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

theorem BookProof.FockNumberPreservingGap.number_quadForm_ge {u : FockAlg} (h0 : u 0 = 0) :
    ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma numberCol u)) : ℂ).re := by sorry
