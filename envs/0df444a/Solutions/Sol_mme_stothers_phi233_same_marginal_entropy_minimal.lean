-- Prove2me | solution 1 for mme_stothers_phi233_same_marginal_entropy_minimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:20:58.512083+00:00
-- url     : https://prove2.me/submissions/f5f3a4e5-cd5e-4d98-8a35-753b527cb7b7

import Theorems.Thm_mme_stothers_phi233_selected_entropy_minimizer_exists

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (E H L : ℝ) (hE : 0 < E) (hH : 0 < H)
    (hEL : E < L) (hHL : H < L) :
    let sigma := 2 * H / (2 * H + L)
    let mu := E / (E + L)
    ∃ a b c d : ℝ,
      0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d ∧
      2 * a + b + c + d = 1 ∧
      2 * a + b = sigma ∧ a + c = mu ∧
      ∀ a' b' c' d' : ℝ,
        0 ≤ a' → 0 ≤ b' → 0 ≤ c' → 0 ≤ d' →
        2 * a' + b' + c' + d' = 1 →
        2 * a' + b' = sigma → a' + c' = mu →
        (-2 * Real.negMulLog a - Real.negMulLog b -
            Real.negMulLog c - Real.negMulLog d) ≤
          (-2 * Real.negMulLog a' - Real.negMulLog b' -
            Real.negMulLog c' - Real.negMulLog d') := by
  dsimp
  obtain ⟨a, ha, hmin⟩ :=
    mme_stothers_phi233_selected_entropy_minimizer_exists
      E H L hE hH hEL hHL
  have ha0 : 0 ≤ a := le_trans (le_max_left 0 _) ha.1
  have haLower :
      2 * H / (2 * H + L) + E / (E + L) - 1 ≤ a :=
    le_trans (le_max_right 0 _) ha.1
  have haSigma : a ≤ (2 * H / (2 * H + L)) / 2 :=
    le_trans ha.2 (min_le_left _ _)
  have haMu : a ≤ E / (E + L) :=
    le_trans ha.2 (min_le_right _ _)
  refine ⟨a,
    2 * H / (2 * H + L) - 2 * a,
    E / (E + L) - a,
    1 - 2 * H / (2 * H + L) - E / (E + L) + a,
    ha0, by linarith, by linarith, by linarith, by ring, by ring, by ring, ?_⟩
  intro a' b' c' d' ha' hb' hc' hd' hsum hsigma hmu
  have ha'Lower :
      2 * H / (2 * H + L) + E / (E + L) - 1 ≤ a' := by
    linarith
  have ha'Sigma : a' ≤ (2 * H / (2 * H + L)) / 2 := by
    linarith
  have ha'Mu : a' ≤ E / (E + L) := by
    linarith
  have ha'Icc :
      a' ∈ Set.Icc
        (max 0 (2 * H / (2 * H + L) + E / (E + L) - 1))
        (min ((2 * H / (2 * H + L)) / 2) (E / (E + L))) :=
    ⟨max_le ha' ha'Lower, le_min ha'Sigma ha'Mu⟩
  have h := hmin a' ha'Icc
  have hbRewrite : 2 * H / (2 * H + L) - 2 * a' = b' := by
    linarith
  have hcRewrite : E / (E + L) - a' = c' := by
    linarith
  have hdRewrite :
      1 - 2 * H / (2 * H + L) - E / (E + L) + a' = d' := by
    linarith
  rw [hbRewrite, hcRewrite, hdRewrite] at h
  exact h
