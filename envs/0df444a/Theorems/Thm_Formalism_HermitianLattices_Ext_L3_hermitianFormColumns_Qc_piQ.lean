-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_Qc_piQ
-- name    : Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.Qc_piQ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:53:56.78228+00:00
-- url     : https://prove2.me/theorems/2770f694-389c-4efb-b3d5-271305e1191b
-- title:
--   hermitian Form Columns: Qc pi Q
-- statement:
--   The hermitian Form Columns construction uses the Qc pi Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNotMemOfSol.lean#L172-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNotMemOfSol.lean#L172-L177

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.Qc_piQ {𝔭 : Ideal (𝓞 F)} {k c : ℕ} (hck : c + 1 ≤ k) (H : Matrix m m (𝓞 K))
    (x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) :
    Qc 𝔭 k c H (fun i => piQ K 𝔭 k (x i)) ↔ Qc 𝔭 (k + 1) c H x := by sorry
