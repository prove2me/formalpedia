-- Prove2me | solution 2 for hurwitz_nonvanishing_limit
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-07T04:53:33.090809+00:00
-- url     : https://prove2.me/submissions/cae0bd0c-3844-42bb-a2f7-5bdb652f513d

import Mathlib

open Complex Finset Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution
    {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf_holo : ∀ n, AnalyticOnNhd ℂ (f n) U)
    (hf_nz : ∀ n, ∀ z ∈ U, f n z ≠ 0)
    (hconv : TendstoUniformlyOn f g atTop U)
    (hg_not_zero : ∃ z ∈ U, g z ≠ 0) :
    ∀ z ∈ U, g z ≠ 0 := by
      -- Assume for contradiction that there exists $z_0 \in U$ such that $g(z_0) = 0$.
      by_contra h_contra;
      -- Choose $r$ small enough that $D(z_0, r) \subset U$ and $g(z) \neq 0$ for all $z \in \overline{D(z_0, r)} \setminus \{z_0\}$.
      obtain ⟨z₀, hz₀U, hz₀⟩ : ∃ z₀ ∈ U, g z₀ = 0 ∧ ∃ r > 0, Metric.closedBall z₀ r ⊆ U ∧ ∀ z ∈ Metric.closedBall z₀ r, z ≠ z₀ → g z ≠ 0 := by
        have h_isolated : ∀ z₀ ∈ U, g z₀ = 0 → ∃ r > 0, ∀ z ∈ Metric.ball z₀ r, z ≠ z₀ → g z ≠ 0 := by
          intros z₀ hz₀U hz₀_zero
          have h_analytic : AnalyticOnNhd ℂ g U := by
            apply_rules [ DifferentiableOn.analyticOnNhd, hconv.tendstoLocallyUniformlyOn.differentiableOn ];
            exact Filter.Eventually.of_forall fun n => ( hf_holo n |> AnalyticOnNhd.differentiableOn );
          have := h_analytic z₀ hz₀U;
          have := this.eventually_eq_zero_or_eventually_ne_zero;
          rcases this with h|h;
          · have h_zero : ∀ z ∈ U, g z = 0 := by
              apply_rules [ h_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero ];
            aesop;
          · rcases Metric.mem_nhdsWithin_iff.mp h with ⟨ r, hr₀, hr ⟩ ; use r ; aesop;
        simp +zetaDelta at *;
        obtain ⟨ z₀, hz₀₁, hz₀₂ ⟩ := h_contra; obtain ⟨ r, hr₀, hr ⟩ := h_isolated z₀ hz₀₁ hz₀₂; rcases Metric.mem_nhds_iff.mp ( hU.mem_nhds hz₀₁ ) with ⟨ ε, εpos, hε ⟩ ; use z₀, hz₀₁, hz₀₂; use Min.min r ε / 2; exact ⟨ by positivity, fun z hz => hε <| Metric.mem_ball.mpr <| by linarith [ min_le_left r ε, min_le_right r ε, Metric.mem_closedBall.mp hz ], fun z hz₁ hz₂ => hr z ( by linarith [ min_le_left r ε, min_le_right r ε, Metric.mem_closedBall.mp hz₁ ] ) hz₂ ⟩ ;
      -- Choose δ = inf { ‖g z‖ : z ∈ Metric.sphere z₀ r } > 0 (positive since g is continuous, the sphere is compact, and g ≠ 0 on the sphere).
      obtain ⟨r, hr_pos, hr_closedBall, hr_sphere⟩ := hz₀.right
      have hδ_pos : ∃ δ > 0, ∀ z ∈ Metric.sphere z₀ r, ‖g z‖ ≥ δ := by
        have hδ_pos : ContinuousOn g (Metric.sphere z₀ r) := by
          have h_cont : ContinuousOn g U := by
            have h_cont : TendstoLocallyUniformlyOn f g atTop U := by
              exact hconv.tendstoLocallyUniformlyOn;
            apply_rules [ h_cont.continuousOn ];
            exact Filter.Eventually.frequently ( Filter.Eventually.of_forall fun n => ( hf_holo n |> AnalyticOnNhd.continuousOn ) );
          exact h_cont.mono ( fun x hx => hr_closedBall <| Metric.sphere_subset_closedBall hx );
        have hδ_pos : ∃ δ ∈ (Set.image (fun z => ‖g z‖) (Metric.sphere z₀ r)), ∀ y ∈ (Set.image (fun z => ‖g z‖) (Metric.sphere z₀ r)), δ ≤ y := by
          apply_rules [ IsCompact.exists_isLeast, CompactIccSpace.isCompact_Icc ];
          · exact IsCompact.image_of_continuousOn ( isCompact_sphere _ _ ) ( hδ_pos.norm );
          · exact ⟨ _, ⟨ z₀ + r, by norm_num [ hr_pos.le ], rfl ⟩ ⟩;
        obtain ⟨ δ, ⟨ z, hzmem, hzgval ⟩, hδ₂ ⟩ := hδ_pos
        have hz0 : z ≠ z₀ := by
          intro h
          exact hr_pos.ne' (by rw [← Metric.mem_sphere.1 hzmem, h, dist_self z₀])
        have hgz : g z ≠ 0 := fun h =>
          hr_sphere z (Metric.sphere_subset_closedBall hzmem) hz0 h
        have hpos : 0 < δ := by
          rw [← hzgval]
          exact norm_pos_iff.mpr hgz
        exact ⟨ δ, hpos, fun z hz => hδ₂ (‖g z‖) ⟨z, hz, rfl⟩ ⟩;
      -- Choose N such that for all n ≥ N, ‖f_n(z) - g(z)‖ < δ/2 for all z ∈ Metric.closedBall z₀ r.
      obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, ∀ z ∈ Metric.closedBall z₀ r, ‖f n z - g z‖ < hδ_pos.choose / 2 := by
        rw [ Metric.tendstoUniformlyOn_iff ] at hconv;
        rcases ( Filter.eventually_atTop ( α := ℕ ) ( p := fun n => ∀ x ∈ U, dist ( g x ) ( f n x ) < hδ_pos.choose / 2 ) ).mp
            ( hconv ( hδ_pos.choose / 2 ) ( half_pos hδ_pos.choose_spec.1 ) ) with ⟨ N, hN ⟩
        exact ⟨ N, fun n hn z hz => by simpa [ dist_eq_norm' ] using hN n hn z ( hr_closedBall hz ) ⟩;
      -- By maximum modulus principle (Complex.norm_le_of_forall_mem_frontier_norm_le): ‖1/f_n(z₀)‖ ≤ max on frontier ≤ 2/δ. So ‖f_n(z₀)‖ ≥ δ/2.
      have h_max_modulus : ∀ n ≥ N, ‖1 / f n z₀‖ ≤ 2 / hδ_pos.choose := by
        intros n hn
        have h_max_modulus_step : ∀ z ∈ Metric.sphere z₀ r, ‖1 / f n z‖ ≤ 2 / hδ_pos.choose := by
          intros z hz
          have h_bound : ‖f n z‖ ≥ hδ_pos.choose / 2 := by
            have := hN n hn z ( Metric.sphere_subset_closedBall hz );
            have := hδ_pos.choose_spec.2 z hz;
            have := norm_sub_le ( f n z ) ( f n z - g z ) ; norm_num at * ; linarith;
          simpa using inv_anti₀ ( half_pos hδ_pos.choose_spec.1 ) h_bound;
        have := @Complex.norm_le_of_forall_mem_frontier_norm_le;
        convert this ( Metric.isBounded_closedBall ) ( show DiffContOnCl ℂ ( fun z => 1 / f n z ) ( Metric.closedBall z₀ r ) from ?_ ) ( show ∀ z ∈ frontier ( Metric.closedBall z₀ r ), ‖1 / f n z‖ ≤ 2 / hδ_pos.choose from ?_ ) ( show z₀ ∈ closure ( Metric.closedBall z₀ r ) from ?_ ) using 1;
        · apply_rules [ DifferentiableOn.diffContOnCl ];
          simp +zetaDelta at *;
          exact DifferentiableOn.inv ( hf_holo n |> AnalyticOnNhd.differentiableOn |> DifferentiableOn.mono <| hr_closedBall ) fun z hz => hf_nz n z <| hr_closedBall hz;
        · simp_all +decide [ frontier_closedBall, hr_pos.ne' ];
        · exact subset_closure ( Metric.mem_closedBall_self hr_pos.le );
      -- But f_n(z₀) → g(z₀) = 0, so ‖f_n(z₀)‖ → 0, contradiction with ‖f_n(z₀)‖ ≥ δ/2.
      have h_contra : Filter.Tendsto (fun n => ‖f n z₀‖) Filter.atTop (nhds 0) := by
        have h_contra : Filter.Tendsto (fun n => f n z₀) Filter.atTop (nhds (g z₀)) := by
          exact hconv.tendsto_at hz₀U;
        simpa [ hz₀.1 ] using h_contra.norm;
      have h_contra : Filter.Tendsto (fun n => ‖1 / f n z₀‖) Filter.atTop Filter.atTop := by
        norm_num +zetaDelta at *;
        refine' Filter.Tendsto.inv_tendsto_nhdsGT_zero _;
        rw [ tendsto_nhdsWithin_iff ];
        exact ⟨ by assumption, Filter.eventually_atTop.mpr ⟨ N, fun n hn => norm_pos_iff.mpr ( hf_nz n z₀ hz₀U ) ⟩ ⟩;
      exact absurd ( h_contra.eventually_gt_atTop ( 2 / hδ_pos.choose ) ) fun h => by have := h.and ( Filter.eventually_ge_atTop N ) ; obtain ⟨ n, hn₁, hn₂ ⟩ := this.exists; linarith [ h_max_modulus n hn₂ ] ;
