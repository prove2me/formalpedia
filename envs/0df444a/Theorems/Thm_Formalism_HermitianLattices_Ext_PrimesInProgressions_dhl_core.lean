-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhl_core
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.dhl_core
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:33:02.926038+00:00
-- url     : https://prove2.me/theorems/2d98272d-2a52-44da-8c55-cc9a847733ef
-- title:
--   Primes In Progressions: dhl core
-- statement:
--   The Primes In Progressions construction uses the dhl core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHLocalB.lean#L27-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHLocalB.lean#L27-L61

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHLocalA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHLocalB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.dhl_core (hCau : DHCauchy) (f : ℂ → ℂ) (t K X : ℝ) (hK : 1 ≤ K) (hX : 3 ≤ X)
    (hf : Differentiable ℂ f) (hf0 : f ((26 / 25 : ℂ) + t * I) ≠ 0)
    (hB : ∀ z, ‖z - ((26 / 25 : ℂ) + t * I)‖ ≤ 12 / 25 →
      ‖f z‖ ≤ K * X ^ 2 * ‖f ((26 / 25 : ℂ) + t * I)‖) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (‖ρ - ((26 / 25 : ℂ) + t * I)‖ ≤ 4 / 25 ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ 150 * (Real.log K + 2) * Real.log X ∧
      ∀ (k : ℕ) (s : ℂ), ‖s - ((26 / 25 : ℂ) + t * I)‖ ≤ 1 / 25 → f s ≠ 0 →
        ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (fun z => -(deriv f z / f z)) s
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)‖ ≤
          150 * (Real.log K + 2) * Real.log X * 25 ^ k := by sorry
