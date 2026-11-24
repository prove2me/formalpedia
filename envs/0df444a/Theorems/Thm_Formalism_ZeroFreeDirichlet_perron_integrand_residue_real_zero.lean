-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_perron_integrand_residue_real_zero
-- name    : Formalism.ZeroFreeDirichlet.perron_integrand_residue_real_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:44:47.402805+00:00
-- url     : https://prove2.me/theorems/21f7d068-c86e-4a0e-a373-256afe5e6a39
-- title:
--   Zero Free Dirichlet: perron integrand residue real zero
-- statement:
--   The Zero Free Dirichlet construction uses the perron integrand residue real zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/RectShiftChi.lean#L55-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/RectShiftChi.lean#L55-L112

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_RectShiftChi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.perron_integrand_residue_real_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {y : ℝ}
    (hy : 0 < y) {β : ℂ} (h0 : 0 < β.re) (h1 : β ≠ 1)
    (hLβ : DirichletCharacter.LFunction χ β = 0)
    (hd : deriv (DirichletCharacter.LFunction χ) β ≠ 0) :
    ∃ A : ℂ → ℂ, DifferentiableAt ℂ A β ∧
      ∀ᶠ z in 𝓝[≠] β, DirichletCharacter.LFunction χ z ≠ 0 ∧
        Fchi χ y z - (-((y : ℂ) ^ β / (β * (β - 1)))) / (z - β) = A z := by sorry
