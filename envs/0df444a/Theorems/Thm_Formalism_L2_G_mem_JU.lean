-- Prove2me | Theorems.Thm_Formalism_L2_G_mem_JU
-- name    : Formalism.L2.G.mem_JU
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:34:31.827811+00:00
-- url     : https://prove2.me/theorems/83267684-4c5c-46e5-b4fa-d9a0448b138e
-- title:
--   G: mem JU
-- statement:
--   The G construction uses the mem JU property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/LevelCharts/SignBlockDeterminant.lean#L281-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/LevelCharts/SignBlockDeterminant.lean#L281-L284

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_LevelCharts_SignBlockDeterminant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField IsDedekindDomain Formalism.UG
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.G
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
  (σE : E →ₐ[F] E) (J : Matrix (Fin N) (Fin N) E) (v : HeightOneSpectrum (𝓞 F))
  (spl : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F) (fr : GL (Fin N) (v.adicCompletion F))

theorem Formalism.L2.G.mem_JU (a t : ℕ) (fixLast : Bool) (fc : ℕ) (x : GL (Fin N) (E ⊗[F] v.adicCompletion F)) :
    x ∈ JU σE J v spl fr a t fixLast fc ↔ x ∈ UPts σE J (v.adicCompletion F) ∧
      fr⁻¹ * bc ((RingHom.fst _ _).comp spl.toRingHom) x * fr ∈ JLoc F v N a t fixLast fc := by sorry
