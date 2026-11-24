-- Prove2me | Theorems.Thm_Formalism_UG_P_sf_bound
-- name    : Formalism.UG.P.sf_bound
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:34:03.996036+00:00
-- url     : https://prove2.me/theorems/f26e3d9a-909d-4b59-8d12-bf28ccb4531e
-- title:
--   P: sf bound
-- statement:
--   The P construction uses the sf bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabfin.lean#L143-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stabfin.lean#L143-L211

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabfin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField ComplexConjugate
open Formalism Formalism.UG Formalism.UG.P
variable {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.sf_bound {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (J : Matrix n n E)
    (τ : E →+* ℂ) (hτ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ)
    (hH : IsHerm (σ : E →+* E) J)
    (hdef : ∀ ι : F →+* ℝ, IsDefiniteAt σ J ι) (g : Matrix n n E)
    (hg : cT (σ : E →+* E) g * J * g = J) (i j : n) :
    ‖τ ((J * g) i j)‖ ≤ ‖τ (J i i)‖ + ‖τ (J j j)‖ := by sorry
