-- Prove2me | Theorems.Thm_Formalism_UG_P_wlocal_map_rowAct
-- name    : Formalism.UG.P.wlocal_map_rowAct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:46.092007+00:00
-- url     : https://prove2.me/theorems/f6db3928-1c29-4a95-ad7c-9c1ca467f118
-- title:
--   P: wlocal map row Act
-- statement:
--   The P construction uses the wlocal map row Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L447-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L447-L457

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

theorem Formalism.UG.P.wlocal_map_rowAct (φ : R →+* S) {r n : ℕ} (g : Matrix (Fin r) (Fin r) R)
    (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (rowAct R g f) = rowAct S (g.map φ) (map φ f) := by sorry
