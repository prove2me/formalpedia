-- Prove2me | Theorems.Thm_Formalism_L2_G_Triv_proG_of
-- name    : Formalism.L2.G.Triv.proG_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:24.817419+00:00
-- url     : https://prove2.me/theorems/47f87489-cdb1-4553-8857-85a2e1392bee
-- title:
--   Triv: pro G of
-- statement:
--   The Triv construction uses the pro G of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/ProGTransfer.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/ProGTransfer.lean#L35-L40

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_ProGTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions
open scoped TensorProduct
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Triv
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}

theorem Formalism.L2.G.Triv.proG_of (h1 : IwProG) (h2 : ProGTransfer) (L : ColLevel R F E sp gp C A clsLat) (hp : ∀ i, (gp i).Prime)
    (hdet : IsUnit sp.gram0.det)
    (halg : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (h : (gp i : 𝓞 F) ∈ v.asIdeal) (a : v.adicCompletion F),
      L.splitG i v h ((1 : E) ⊗ₜ[F] a) = (a, a)) : L.ProG := by sorry
