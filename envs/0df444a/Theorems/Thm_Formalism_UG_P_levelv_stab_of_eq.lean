-- Prove2me | Theorems.Thm_Formalism_UG_P_levelv_stab_of_eq
-- name    : Formalism.UG.P.levelv_stab_of_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:33:13.294803+00:00
-- url     : https://prove2.me/theorems/6123283c-808b-4bed-ad35-941e57569a3e
-- title:
--   P: levelv stab of eq
-- statement:
--   The P construction uses the levelv stab of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean#L284-L320
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelv.lean#L284-L320

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG

theorem Formalism.UG.P.levelv_stab_of_eq {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (Λ : Set (n → R)) (N : ℕ) (hinj : ∀ y y' : n → R, N • y = N • y' → y = y') (ga a b : GL n R)
    (hZ : (fun x => N • ((a : Matrix n n R) *ᵥ ((ga : Matrix n n R) *ᵥ x))) '' Λ =
      (fun x => N • ((b : Matrix n n R) *ᵥ ((ga : Matrix n n R) *ᵥ x))) '' Λ) (x : n → R) :
    x ∈ Λ ↔ ((ga⁻¹ * (a⁻¹ * b) * ga : GL n R) : Matrix n n R) *ᵥ x ∈ Λ := by sorry
