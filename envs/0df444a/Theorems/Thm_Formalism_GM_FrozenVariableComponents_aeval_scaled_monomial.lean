-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_aeval_scaled_monomial
-- name    : Formalism.GM.FrozenVariableComponents.aeval_scaled_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:56.693792+00:00
-- url     : https://prove2.me/theorems/3460cde6-c96e-49a0-8785-7fd19f77b781
-- title:
--   Frozen Variable Components: aeval scaled monomial
-- statement:
--   The Frozen Variable Components construction uses the aeval scaled monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L745-L767
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L745-L767

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.FrozenVariableComponents.aeval_scaled_monomial (ρ : Fin r) (m : Fin N × Fin r →₀ ℕ) (a : ℚ_[p]) :
    aeval (fun x : Fin N × Fin r => (X (Fin.last N, ρ) * X (emb x) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]))
      (monomial m a) = X (Fin.last N, ρ) ^ m.degree * monomial (Finsupp.mapDomain emb m) a := by sorry
