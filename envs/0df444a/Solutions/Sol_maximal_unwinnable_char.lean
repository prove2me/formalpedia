-- Prove2me | solution 1 for maximal_unwinnable_char
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:53:35.016328+00:00
-- url     : https://prove2.me/submissions/6f5eb6bf-5952-4bfe-bfa6-000fdb00a4dd

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
public import Theorems.Thm_winnable_of_deg_ge_genus
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_effective_of_winnable_and_q_reduced
public import Theorems.Thm_legal_set_empty
public import Theorems.Thm_maximal_superstable_exists
public import Theorems.Thm_maximal_superstable_orientation
public import Theorems.Thm_maximal_unwinnable_preserved
public import Theorems.Thm_q_reduced_eq_chips_sub_one_chip
public import Theorems.Thm_q_reduced_toConfig_superstable
public import Theorems.Thm_superstable_sub_chip_unwinnable
public import Theorems.Thm_winnable_add_winnable
public import Theorems.Thm_winnable_of_effective
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty


section
@[expose] public section
set_option trace.split.failure true
open Multiset Finset
private lemma maximal_unwinnable_q_reduced_chips_at_q (G : CFGraph) (q : G.V) (D : CFDiv G) :
  maximal_unwinnable G D → q_reduced G q D → D q = -1 := by
  intro h_max_unwin h_qred
  have h_neg : D q < 0 := by
    contrapose! h_max_unwin
    unfold maximal_unwinnable
    push Not
    intro h_unwin
    absurd h_unwin
    suffices effective D by
      exact winnable_of_effective G D this
    intro v
    by_cases hv : v = q
    · rw [hv]
      exact h_max_unwin
    · exact h_qred.1 v (by simp only [ne_eq, hv, not_false_eq_true])
  have h_add_win : winnable G (D + one_chip q) := by exact (h_max_unwin.2 q)
  have h_eff : effective (D + one_chip q) := by
    apply effective_of_winnable_and_q_reduced G q (D + one_chip q) h_add_win
    -- Prove q-reducedness of D + one_chip q
    constructor
    · intro v hv
      have h_v_ne_q : v ≠ q := by
        exact Set.mem_ofPred.mp hv
      rw [Pi.add_apply]
      simp only [ne_eq, h_v_ne_q, not_false_eq_true, one_chip_apply_other', add_zero, ge_iff_le]
      apply h_qred.1 v hv
    · intro S hq hS_nonempty hlegal
      apply h_qred.2 S hq hS_nonempty
      intro v hv_in_S
      have hvq : v ≠ q := fun hvq => hq (hvq ▸ hv_in_S)
      simpa only [Pi.add_apply, one_chip_apply_other' q v hvq, add_zero] using
        hlegal v hv_in_S
  have h_nonneg : D q + 1 ≥ 0 := by
    have h := h_eff q
    rw [Pi.add_apply] at h
    simp only [one_chip_apply_v, ge_iff_le] at h
    exact h
  linarith
private lemma degree_max_superstable {G : CFGraph} {q : G.V} (c : Config G q) (h_max : maximal_superstable G c): config_degree c = genus G := by
  have := maximal_superstable_orientation G q c h_max
  rcases this with ⟨O, hO, h_orient_eq⟩
  rw [← h_orient_eq]
  exact config_degree_from_O O hO
private lemma maximal_superstable_chip_winnable {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (c' : Config G q) :
  maximal_superstable G c' →
  ∀ (v : G.V), winnable G (c'.chips- (one_chip q) + (one_chip v)) := by
  intro h_max_superstable v
  let D' := c'.chips - one_chip q + one_chip v
  have deg_ineq : deg D' ≥ genus G := by
    calc
      deg D' = config_degree c' := by
        dsimp only [D']
        simp only [_root_.map_add, deg_chips_sub_one_chip, config_degree, deg_one_chip,
            sub_add_cancel]
      _ = genus G := degree_max_superstable c' h_max_superstable
      _ ≥ genus G := by rfl
  exact winnable_of_deg_ge_genus h_conn D' deg_ineq
private lemma maximal_unwinnable_q_reduced_toConfig_form {G : CFGraph} (q : G.V) (D : CFDiv G)
    (h_max : maximal_unwinnable G D) (h_qred : q_reduced G q D) :
    D = (toConfig ⟨D, h_qred.1⟩).chips - one_chip q := by
  exact q_reduced_eq_chips_sub_one_chip G q D h_qred
    (maximal_unwinnable_q_reduced_chips_at_q G q D h_max h_qred)
private lemma maximal_unwinnable_of_maximal_superstable_form {G : CFGraph}
    (h_conn : graph_connected G) (q : G.V) (c : Config G q) :
    maximal_superstable G c → maximal_unwinnable G (c.chips - one_chip q) := by
  intro h_max_c
  refine ⟨superstable_sub_chip_unwinnable q c h_max_c.1, ?_⟩
  intro v
  exact maximal_superstable_chip_winnable h_conn q c h_max_c v
private lemma maximal_unwinnable_q_reduced_toConfig_iff {G : CFGraph}
    (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) (h_qred : q_reduced G q D) :
    maximal_unwinnable G D ↔
    maximal_superstable G (toConfig ⟨D, h_qred.1⟩) ∧
    D = (toConfig ⟨D, h_qred.1⟩).chips - one_chip q := by
  constructor
  · intro h_max
    constructor
    · let c : Config G q := toConfig ⟨D, h_qred.1⟩
      have h_super_c : superstable G q c := q_reduced_toConfig_superstable G q D h_qred
      have h_form_D : D = c.chips - one_chip q := by
        exact maximal_unwinnable_q_reduced_toConfig_form q D h_max h_qred
      by_contra h_not_max_c
      rcases maximal_superstable_exists G q c h_super_c with ⟨c', h_max_c', h_ge⟩
      have h_ne : c' ≠ c := by
        intro h_eq
        apply h_not_max_c
        simpa only [h_eq] using h_max_c'
      have h_strict : ∃ v : G.V, c.chips v + 1 ≤ c'.chips v := by
        by_contra h_no
        push Not at h_no
        have h_c'_le_c : c' ≤ c := by
          intro v
          linarith [h_no v]
        exact h_ne ((le_antisymm h_ge h_c'_le_c).symm)
      rcases h_strict with ⟨v, h_v_strict⟩
      have h_H_eff : effective (c'.chips - c.chips - one_chip v) := by
        intro w
        by_cases h_wv : w = v
        · rw [h_wv]
          simp only [Pi.sub_apply, one_chip, ↓reduceIte, Int.sub_nonneg]
          linarith [h_ge v, h_v_strict]
        · simp only [Pi.sub_apply, one_chip, h_wv, ↓reduceIte, sub_zero, Int.sub_nonneg]
          linarith [h_ge w]
      have h_D''_eq :
          c'.chips - one_chip q =
            (c'.chips - c.chips - one_chip v) + (D + one_chip v) := by
        rw [h_form_D]
        funext w
        simp only [Pi.sub_apply, sub_eq_add_neg, Pi.add_apply, Pi.neg_apply]
        abel_nf
      have h_D''_unwin : ¬winnable G (c'.chips - one_chip q) :=
        superstable_sub_chip_unwinnable q c' h_max_c'.1
      apply h_D''_unwin
      rw [h_D''_eq]
      exact winnable_add_winnable G (c'.chips - c.chips - one_chip v) (D + one_chip v)
        (winnable_of_effective G _ h_H_eff) (h_max.2 v)
    · exact maximal_unwinnable_q_reduced_toConfig_form q D h_max h_qred
  · rintro ⟨h_max_c, h_form⟩
    rw [h_form]
    exact maximal_unwinnable_of_maximal_superstable_form h_conn q _ h_max_c
end
end

set_option autoImplicit true
@[expose] public section
public section
set_option trace.split.failure true
open Multiset Finset
theorem _root_.solution {G : CFGraph} (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
  maximal_unwinnable G D ↔
    maximal_superstable G (qReducedConfig h_conn q D) ∧
    qReducedRep h_conn q D =
      (qReducedConfig h_conn q D).chips - one_chip q := by
  let D' := qReducedRep h_conn q D
  have h_qred_D' : q_reduced G q D' := (qReducedRep_spec h_conn q D).2
  have h_core := maximal_unwinnable_q_reduced_toConfig_iff h_conn q D' h_qred_D'
  constructor
  · intro h_max_unwinnable_D
    have h_max_D' : maximal_unwinnable G D' :=
      maximal_unwinnable_preserved G D D' h_max_unwinnable_D (qReducedRep_spec h_conn q D).1
    simpa only [qReducedConfig] using h_core.mp h_max_D'
  · intro h_can
    have h_max_D' : maximal_unwinnable G D' := by
      simpa only using h_core.mpr h_can
    exact maximal_unwinnable_preserved G D' D h_max_D' (qReducedRep_spec h_conn q D).1.symm
