-- Prove2me | solution 1 for quantum_minor_skip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:22:16.066615+00:00
-- url     : https://prove2.me/submissions/5698943f-e1c0-41a8-8f37-3605e5156052

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkipSuccessorIndex_SkipSucc2
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmSkip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.QmSkip := by
  have hsa : ∀ {n : ℕ} (p : Fin (n + 1)) (k : Fin n),
      (p.succAbove k).val = if k.val < p.val then k.val else k.val + 1 := by
    intro n p k
    unfold Fin.succAbove
    split_ifs with h1 h2 h2 <;> simp_all [Fin.lt_def]
  refine ⟨fun t i j => ?_, fun t i i' j hii' => ?_⟩
  · apply Fin.ext
    have e := hsa i j
    unfold PI.skip1
    split_ifs at e ⊢ <;> simp only at * <;> omega
  · apply Fin.ext
    have e1 := hsa i i'
    have e2 := hsa i' j
    have e3 := hsa i (i'.succAbove j)
    rw [if_neg (by omega)] at e1
    unfold PI.skip2
    split_ifs at e2 e3 ⊢ <;> simp only at * <;> omega
