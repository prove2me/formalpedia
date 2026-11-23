-- Prove2me | Theorems.Thm_Formalism_UG_P_wlocal_map_lpMinor
-- name    : Formalism.UG.P.wlocal_map_lpMinor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:33.345239+00:00
-- url     : https://prove2.me/theorems/1a699e48-1f5b-4e9d-9146-6754ab1d7d29
-- title:
--   P: wlocal map lp Minor
-- statement:
--   The P construction uses the wlocal map lp Minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L409-L415
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L409-L415

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.GradedWeylDivisibility
variable {R S : Type} [CommRing R] [CommRing S]

theorem Formalism.UG.P.wlocal_map_lpMinor (φ : R →+* S) {r n : ℕ} (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    map φ (lpMinor R (r := r) (n := n) s hr hn) = lpMinor S s hr hn := by sorry
