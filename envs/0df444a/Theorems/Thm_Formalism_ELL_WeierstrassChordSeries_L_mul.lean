-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_L_mul
-- name    : Formalism.ELL.WeierstrassChordSeries.L_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:50.693373+00:00
-- url     : https://prove2.me/theorems/bc8298a1-596b-4232-9baf-84bdae02c9cc
-- title:
--   Weierstrass Chord Series: L mul
-- statement:
--   The Weierstrass Chord Series construction uses the L mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L372-L424
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L372-L424

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff

theorem Formalism.ELL.WeierstrassChordSeries.L_mul (φ ψ : MvPowerSeries (Fin 2) K) (i : Fin 2) :
    (L i) (φ * ψ) = cc φ * (L i) ψ + (L i) φ * cc ψ := by sorry
