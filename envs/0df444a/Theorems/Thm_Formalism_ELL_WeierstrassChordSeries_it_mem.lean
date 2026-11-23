-- Prove2me | Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_it_mem
-- name    : Formalism.ELL.WeierstrassChordSeries.it_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:19:33.788121+00:00
-- url     : https://prove2.me/theorems/055e9a24-c4f3-47b5-81dd-9bdceb17b8b2
-- title:
--   Weierstrass Chord Series: it mem
-- statement:
--   The Weierstrass Chord Series construction uses the it mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L222-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/WChord.lean#L222-L242

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
variable {K : Type u} [Field K] (W : WeierstrassCurve K)
variable {W}

theorem Formalism.ELL.WeierstrassChordSeries.it_mem (S : Subalgebra ℤ K) (hS : ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K) ⊆ S) :
    ∀ k, it W k ∈ (PowerSeries.map (algebraMap S K)).range := by sorry
