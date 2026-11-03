-- Prove2me | solution 1 for finite_of_nilpotent_fg_order
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-02T23:18:58.591052+00:00
-- url     : https://prove2.me/submissions/4c023f73-1c86-47d9-8646-d72603bcb2bf

import Mathlib

section
-- module Solutions.OAIQ093_PR.NilpotentFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


open scoped IsMulCommutative

lemma finite_of_nilpotent_fg_order_oai {G: Type*} [Group G] [Group.FG G] [Group.IsNilpotent G] (hG: Monoid.IsTorsion G): Finite G := by
  induction' n : Group.nilpotencyClass G with n ih generalizing G <;> simp_all +decide [ Group.nilpotencyClass ];
  · rw [ eq_top_iff ] at n ; aesop;
    -- Since the top subgroup is equal to the bottom subgroup, G must be trivial.
    have h_trivial : ∀ g : G, g = 1 := by
      simp_all +decide [ Subgroup.eq_bot_iff_forall ];
    exact Set.finite_univ_iff.mp ( Set.Finite.subset ( Set.finite_singleton 1 ) fun g _ => h_trivial g );
  · -- The quotient group $G/Z(G)$ is finitely generated (as a quotient of a finitely generated group) and nilpotent.
    have h_quot_finite : Finite (G ⧸ Subgroup.center G) := by
      -- By the induction hypothesis, $G/Z(G)$ is finite.
      refine ih inferInstance ?_ ?_
      ·
        intro g
        specialize hG g.out
        rw [isOfFinOrder_iff_pow_eq_one]
        rw [isOfFinOrder_iff_pow_eq_one] at hG
        obtain ⟨n, hn⟩ := hG
        use n
        refine ⟨hn.1, ?_⟩
        rw [← QuotientGroup.out_eq' (a := g)]
        erw [ QuotientGroup.eq_one_iff ]
        simp [hn.2]
      · have e := nilpotencyClass_quotient_center (G := G)
        have hq : Group.IsNilpotent (G ⧸ Subgroup.center G) := inferInstance
        simp_all +decide [Group.nilpotencyClass]
    -- Since $Z(G)$ is finitely generated and torsion, it is finite.
    have h_center_finite : Finite (Subgroup.center G) := by
      -- Since $Z(G)$ is finitely generated and torsion, it is finite by the structure theorem for finitely generated abelian groups.
      have h_center_finite : Group.FG (Subgroup.center G) := by
        convert Subgroup.fg_of_index_ne_zero ?_;
        · infer_instance;
        · exact Subgroup.finiteIndex_iff_finite_quotient.mpr h_quot_finite;
      have h_center_torsion : Monoid.IsTorsion (↥(Subgroup.center G)) := by
        intro x;
        rw [isOfFinOrder_iff_pow_eq_one]
        specialize hG x
        rw [isOfFinOrder_iff_pow_eq_one] at hG
        obtain ⟨n, hn⟩ := hG
        use n
        refine ⟨hn.1, ?_⟩
        rw [Subtype.ext_iff]
        simp
        exact hn.2
      exact CommGroup.finite_of_fg_torsion (↥(Subgroup.center G)) h_center_torsion;
    convert Finite.of_subgroup_quotient ( H := Subgroup.center G )
end

theorem solution.{u_1} : type_of% @finite_of_nilpotent_fg_order_oai.{u_1} := @finite_of_nilpotent_fg_order_oai.{u_1}
