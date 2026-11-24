-- Prove2me | solution 1 for qnEabGl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:06:46.198518+00:00
-- url     : https://prove2.me/submissions/46421991-5238-48b0-ab92-478c1592e18a

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ElementaryGeneratorsLevelGroup
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnEabGl
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_ec_comm
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_ec_sub
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_ec_zero
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_hpart_mem
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_inV_single
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_inV_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
private lemma single_one_mul_single_one {n : ℕ} (p q s t : Fin n) :
    Matrix.single p q (1 : ℂ) * Matrix.single s t 1 = if q = s then Matrix.single p t 1 else 0 := by
  split_ifs with h
  · subst h
    rw [Matrix.single_mul_single_same, mul_one]
  · exact Matrix.single_mul_single_of_ne (h := h) ..
private lemma posL_eq_posL_iff (k r : ℕ) (i : Fin (r + 1)) (x y : Fin (Formalism.FourierDecayAlt.Q.mdim k r i)) :
    Formalism.FourierDecayAlt.Q.posL k r i x = Formalism.FourierDecayAlt.Q.posL k r i y ↔ x = y := by
  constructor
  · intro h
    have h' := congrArg Fin.val h
    simp only [Formalism.FourierDecayAlt.Q.posL] at h'
    exact Fin.ext (by omega)
  · rintro rfl
    rfl
end

set_option autoImplicit false

theorem _root_.solution : Formalism.FourierDecayAlt.Q.EabGlLev := by
  intro E _ _ k r i D a b c d f _ hf g hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hL : Formalism.FourierDecayAlt.Q.EabGlW.LocExt (Formalism.FourierDecayAlt.Q.Glev k r i) f F U := ⟨hU, hF, hfF⟩
  have good : ∀ x y : Fin (Formalism.FourierDecayAlt.Q.mdim k r i), Formalism.FourierDecayAlt.Q.EabGlW.Good k r i
      (Matrix.single (Formalism.FourierDecayAlt.Q.posL k r i x) (Formalism.FourierDecayAlt.Q.posL k r i y) (1 : ℂ)) :=
    fun x y => Formalism.FourierDecayAlt.Q.EabGlW.hpart_mem (Formalism.FourierDecayAlt.Q.EabGlW.inV_single x y)
  have good0 : Formalism.FourierDecayAlt.Q.EabGlW.Good k r i (0 : Formalism.FourierDecayAlt.Q.Mx k r) :=
    Formalism.FourierDecayAlt.Q.EabGlW.hpart_mem Formalism.FourierDecayAlt.Q.EabGlW.inV_zero
  have goodIf : ∀ (P : Prop) [Decidable P] (x y : Fin (Formalism.FourierDecayAlt.Q.mdim k r i)),
      Formalism.FourierDecayAlt.Q.EabGlW.Good k r i (if P then
        Matrix.single (Formalism.FourierDecayAlt.Q.posL k r i x) (Formalism.FourierDecayAlt.Q.posL k r i y) (1 : ℂ) else 0) := by
    intro P _ x y
    split_ifs
    · exact good x y
    · exact good0
  have hcomm := Formalism.FourierDecayAlt.Q.EabGlW.ec_comm (good a b) (good c d) hL hgU hg.1
  rw [single_one_mul_single_one, single_one_mul_single_one] at hcomm
  simp only [posL_eq_posL_iff] at hcomm
  rw [Formalism.FourierDecayAlt.Q.EabGlW.ec_sub (goodIf _ a d) (goodIf _ c b) hL hgU hg.1] at hcomm
  change _ = _ at hcomm
  refine hcomm.trans ?_
  congr 1
  · split_ifs
    · rfl
    · exact Formalism.FourierDecayAlt.Q.EabGlW.ec_zero f g
  · split_ifs
    · rfl
    · exact Formalism.FourierDecayAlt.Q.EabGlW.ec_zero f g
