-- Prove2me | Theorems.Thm_Formalism_L2_Pj_SatLin_exists_basis_of_saturated
-- name    : Formalism.L2.Pj.SatLin.exists_basis_of_saturated
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:06.655798+00:00
-- url     : https://prove2.me/theorems/047adfdc-fa8a-4d86-9b2f-d27162e1b3d4
-- title:
--   Sat Lin: exists basis of saturated
-- statement:
--   The Sat Lin construction uses the exists basis of saturated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExistsBasisOfSaturated.lean#L9-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ExistsBasisOfSaturated.lean#L9-L73

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExistsBasisOfSaturated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.SatLin

theorem Formalism.L2.Pj.SatLin.exists_basis_of_saturated {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {d r : ℕ}
    (u : Fin r → (Fin d → R)) (hu : LinearIndependent R u)
    (hs : ∀ (v : Fin d → R) (a : R), a ≠ 0 → a • v ∈ Submodule.span R (Set.range u) →
      v ∈ Submodule.span R (Set.range u)) :
    ∃ (w : Fin d → Fin d → R) (emb : Fin r ↪ Fin d), (∀ i, w (emb i) = u i) ∧
      ∀ v : Fin d → R, ∃! a : Fin d → R, ∀ j, ∑ k, a k * w k j = v j := by sorry
