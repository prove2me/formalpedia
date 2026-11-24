-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_fock_expand
-- name    : Formalism.GM.GammaExpansion.fock_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:30.355258+00:00
-- url     : https://prove2.me/theorems/ffe71dc6-b08a-4d4b-b118-f27a4a5c8028
-- title:
--   Gamma Expansion: fock expand
-- statement:
--   The Gamma Expansion construction uses the fock expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L1029-L1049
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L1029-L1049

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
variable (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}

theorem Formalism.GM.GammaExpansion.fock_expand (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d) (ρ : Fin r)
    (q y : MvPolynomial σ ℚ_[p]) (K : ℕ) (hq : ∀ s ∈ q.support, s (e ρ) ≤ K) (o' n' z' s m : ℕ) :
    M.fock p (X (e ρ) ^ m * y) ((tieE w e ^ s) (tiePhi w e o' n' z' (X (e ρ) ^ m * q))) =
      ∑ j ∈ range (o' + 1), cph ℚ_[p] (o' + n' + r + z' - 1) j * ((m.factorial : ℚ_[p]) *
        ∑ i ∈ range (s + j + 1), ∑ t ∈ range (K + 1),
          (((m.choose i * (m - i).choose t : ℕ) : ℚ_[p]) * ((s + j).descFactorial i : ℚ_[p]) /
            ((i + t).factorial : ℚ_[p])) *
          M.fock p y (X (w ρ) ^ i * (∑ c, X (w c) * X (e c)) ^ (s + j - i) *
            (tieF w e ^ j) (X (e ρ) ^ (i + t) * (Dp (e ρ) ^ t) q))) := by sorry
