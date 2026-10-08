-- Prove2me | Theorems.Thm_ConnesGreen_RG0Integration_sourceEmbed_L_energyVector
-- name    : ConnesGreen.RG0Integration.sourceEmbed_L_energyVector
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-07T22:45:11.306178+00:00
-- url     : https://prove2.me/theorems/a290cebc-89a8-4b03-9858-f5e01310a3cc
-- title:
--   Original Riesz source of Lg equals its Dirichlet energy vector
-- statement:
--   For $t>0$ and an original admissible test supported in $(-t,t)$, the original Riesz source representative satisfies $$\operatorname{sourceEmbed}_t(Lg)=\operatorname{energyVector}_t(g)$$ in the original two-component ambient Hilbert space. The energy vector consists of the original restricted derivative and one half of the original restricted test. The proof is recovered from the accepted RG-3 proof using the original derivative probe, integration by parts, orthogonality and Riesz projection. The physical carrier and metric are unchanged; no column or positivity premise is assumed.
-- source:
--   Exact original accepted RG-3 source custody and native CanonicalGreenAnalysis.lean, sourceEmbed_L. Nine supporting declaration spans are extracted by Lean dependency and syntax metadata; constructor bodies are retained in the separate original probe interface.

import Definitions.Def_ConnesGreen_canonical_model
set_option autoImplicit false
open ConnesGreen WeilDefect WeilDefect.ConnesNative
noncomputable section

theorem ConnesGreen.RG0Integration.sourceEmbed_L_energyVector (t : ℝ) (ht : 0 < t)
    (g : ℝ → ℂ) (hg : SupportedTest t g) :
    (sourceEmbed t (problemOneL g) : Ambient t) = energyVector t g := by sorry
