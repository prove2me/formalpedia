-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_jac_eisG
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.jac_eisG
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:37:28.783127+00:00
-- url     : https://prove2.me/theorems/91ff4bdd-b729-4dc9-8922-d8ec0b1ac547
-- title:
--   B5: jac eis G
-- statement:
--   The B5 construction uses the jac eis G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/Jacobi.lean#L57-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/EpsteinZeta/Jacobi.lean#L57-L88

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_DedekindFactorK
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_EpsteinZeta_Jacobi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.jac_eisG (a z : ℂ) (ha : a ≠ 0) (hz : 0 < z.im) (k : ℕ) (hk : k ≠ 0) :
    eisG (AddSubgroup.closure {a, a * z}) k =
      (a ^ (2 * k))⁻¹ * ∑' v : Fin 2 → ℤ,
        EisensteinSeries.eisSummand ((2 * k : ℕ) : ℤ) v (⟨z, hz⟩ : UpperHalfPlane) := by sorry
