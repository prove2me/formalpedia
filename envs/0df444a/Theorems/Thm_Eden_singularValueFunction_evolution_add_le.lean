-- Prove2me | Theorems.Thm_Eden_singularValueFunction_evolution_add_le
-- name    : Eden.singularValueFunction_evolution_add_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:37:13.664914+00:00
-- url     : https://prove2.me/theorems/2bca862b-271e-5e87-9578-6d52ae30c504
-- title:
--   Eden: singular Value Function evolution add le
-- statement:
--   The Eden construction uses the singular Value Function evolution add le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorCocycle.lean#L44-L50
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExteriorCocycle.lean#L44-L50

import Definitions.Def_Eden_ExteriorSingularValues
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_ExteriorCocycle
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.singularValueFunction_evolution_add_le {k : ℕ} (hk : k ≤ 5) (c : ℝ)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (p : PhaseSpace) :
    singularValueFunction (fderiv ℝ (evolution c (s + t)) p).toLinearMap k ≤
      singularValueFunction (fderiv ℝ (evolution c t) (evolution c s p)).toLinearMap k *
        singularValueFunction (fderiv ℝ (evolution c s) p).toLinearMap k := by sorry
