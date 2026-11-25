-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_PCountEx_approx_lo
-- name    : Formalism.L2.SG.Pf.PCountEx.approx_lo
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:17:13.246816+00:00
-- url     : https://prove2.me/theorems/a36b09ff-ee0f-4df3-86d4-50d8dbe04764
-- title:
--   PCount Ex: approx lo
-- statement:
--   The PCount Ex construction uses the approx lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IotaFIntMem.lean#L189-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/IotaFIntMem.lean#L189-L213

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_WithZeroLeOneEqExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_IotaFIntMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open NumberField IsDedekindDomain ValuativeRel
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.PCountEx
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  (A : ∀ p : HeightOneSpectrum (𝓞 F), Formalism.MainNotions.S.Loc.LocAt F E sig p) {n : ℕ}

theorem Formalism.L2.SG.Pf.PCountEx.approx_lo (S : Finset (HeightOneSpectrum (𝓞 F))) (c : 𝓞 F) (hc : c ≠ 0)
    (g : ∀ p, Matrix (Fin n) (Fin n) (A p).Ep) (hg1 : ∀ p ∈ S, ∀ a, g p a a = 1)
    (hg0 : ∀ p ∈ S, ∀ a b, a < b → g p a b = 0) :
    ∃ L : Matrix (Fin n) (Fin n) E, (∀ a, L a a = 1) ∧ (∀ a b, a < b → L a b = 0) ∧
      (∀ p ∈ S, ∀ a b, ∃ o ∈ (A p).O,
        (A p).ιE (L a b) - g p a b = algebraMap (A p).Fp (A p).Ep ((A p).ιF (algebraMap (𝓞 F) F c)) * o) ∧
      ∀ p ∉ S, ∀ a b, (A p).ιE (L a b) ∈ (A p).O := by sorry
