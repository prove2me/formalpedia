-- Prove2me | Theorems.Thm_Formalism_UG_P_wlocal_loc
-- name    : Formalism.UG.P.wlocal_loc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:38:29.269941+00:00
-- url     : https://prove2.me/theorems/595e3070-a651-4c89-a6b8-3358211f180b
-- title:
--   P: wlocal loc
-- statement:
--   The P construction uses the wlocal loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L486-L535
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Wlocal.lean#L486-L535

import Definitions.Def_Formalism_SatakeDualWeyl_StatementW
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Wlocal
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

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
variable {R : Type} [CommRing R]

theorem Formalism.UG.P.wlocal_loc (P : Ideal R) [P.IsPrime] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (x : MvPolynomial (Fin r × Fin n) R)
    (hx : map (algebraMap R (Localization.AtPrime P)) x ∈ weyl (Localization.AtPrime P) r n hn ν) :
    ∃ t ∈ P.primeCompl, C t * x ∈ weyl R r n hn ν := by sorry
