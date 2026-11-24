-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_Z_biHom
-- name    : Formalism.GM.GammaExpansion.Z_biHom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:20.222842+00:00
-- url     : https://prove2.me/theorems/f4b312e2-d6cf-4b22-8c2c-73b67b2c2e6c
-- title:
--   Gamma Expansion: Z bi Hom
-- statement:
--   The Gamma Expansion construction uses the Z bi Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L977-L1004
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L977-L1004

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.GammaExpansion.Z_biHom (LL : M.Letters (N + 1)) (ρ : Fin r) (e : ℕ) (he : e ≤ LL.deg (Fin.last N))
    (h : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) (hh : h ∈ M.Pol p r (lowerLast LL e)) (m0 : ℕ) :
    BiHom (fun c : Fin r => (Fin.castSucc (Fin.last N), c)) (fun c : Fin r => (Fin.last (N + 1), c))
      (LL.deg (Fin.last N) - e) (m0 + (LL.total - e))
      (X (Fin.last (N + 1), ρ) ^ m0 * aeval (M.freezeSub p LL ρ) h) := by sorry
