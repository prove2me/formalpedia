-- Prove2me | solution 1 for entropy_convexity_refinement_marginal_le_integral_fiber
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-24T15:49:05.473262+00:00
-- url     : https://prove2.me/submissions/6223946a-7e8d-4eba-8196-cf5951b341f9

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real MeasureTheory

/-- **The convexity refinement of the entropy functional.**

`Ent_μ(g₁) ≤ ∫_y Ent_μ(f(·,y)) dν`, where `g₁ x = ∫_y f(x,y) dν`.

This is the Jensen / convexity inequality for the entropy functional applied to the
inner integral.  It follows from the pointwise (in `x`) log-sum inequality
`g₁(x) log(g₁(x)/M) ≤ ∫_y f(x,y) log(f(x,y)/m_y) dν`, proved by the scalar Gibbs /
Bregman inequality with reference `b(y) = g₁(x)·m_y/M`, integrated over `x` and
Fubini-swapped.  `M = ∫_x g₁ x dμ = ∫_y m_y dν`, `m_y = ∫_x f(x,y) dμ`.

Source: Boucheron–Lugosi–Massart, *Concentration Inequalities* (OUP 2013),
Theorem 4.10 (sub-additivity of entropy) — the two-block / convexity form. -/
theorem solution
    {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α × β → ℝ}
    (hf_pos : ∀ p, 0 < f p)
    (hf_int : Integrable f (μ.prod ν))
    (hflog_int : Integrable (fun p ↦ f p * Real.log (f p)) (μ.prod ν))
    (hg1log_int : Integrable (fun x ↦ (∫ y, f (x, y) ∂ν) * Real.log (∫ y, f (x, y) ∂ν)) μ)
    (hm_int : Integrable (fun y ↦ ∫ x, f (x, y) ∂μ) ν)
    (hfx_int : ∀ x, Integrable (fun y ↦ f (x, y)) ν)
    (hfx_logm_int : ∀ x, Integrable (fun y ↦ f (x, y) * Real.log (∫ x', f (x', y) ∂μ)) ν)
    (hfx_logf_int : ∀ x, Integrable (fun y ↦ f (x, y) * Real.log (f (x, y))) ν)
    (h_inner_x_int :
      Integrable (fun x ↦ ∫ y, (f (x, y) * Real.log (f (x, y))
        - f (x, y) * Real.log (∫ x', f (x', y) ∂μ)) ∂ν) μ)
    (hfm_prod_int :
      Integrable (fun p : α × β ↦ f p * Real.log (∫ x', f (x', p.2) ∂μ)) (μ.prod ν)) :
    ( (∫ x, (∫ y, f (x, y) ∂ν) * Real.log (∫ y, f (x, y) ∂ν) ∂μ)
        - (∫ x, (∫ y, f (x, y) ∂ν) ∂μ) * Real.log (∫ x, (∫ y, f (x, y) ∂ν) ∂μ) )
    ≤ ∫ y, ( (∫ x, f (x, y) * Real.log (f (x, y)) ∂μ)
              - (∫ x, f (x, y) ∂μ) * Real.log (∫ x, f (x, y) ∂μ) ) ∂ν := by
  -- Scalar Gibbs / Bregman inequality for `t log t` (inlined).
  have scalar_gibbs : ∀ {y u : ℝ}, 0 ≤ y → 0 < u →
      0 ≤ y * Real.log y - y * Real.log u - (y - u) := by
    intro y u hy hu
    rcases eq_or_lt_of_le hy with hy0 | hy0
    · subst hy0; simp; exact hu.le
    · have hdual0 : 1 - (y / u)⁻¹ ≤ Real.log (y / u) :=
        Real.one_sub_inv_le_log_of_pos (by positivity)
      rw [Real.log_div (ne_of_gt hy0) (ne_of_gt hu)] at hdual0
      have hinv : (y / u)⁻¹ = u / y := by rw [inv_div]
      rw [hinv] at hdual0
      have hmul : y * (1 - u / y) ≤ y * (Real.log y - Real.log u) :=
        mul_le_mul_of_nonneg_left hdual0 hy0.le
      have heq : y * (1 - u / y) = y - u := by field_simp
      rw [heq] at hmul
      nlinarith [hmul]
  -- For a probability measure, the integral of a strictly positive integrable function
  -- is strictly positive (inlined helpers, one per index type).
  have ipos_α : ∀ {h : α → ℝ}, (∀ x, 0 < h x) → Integrable h μ → 0 < ∫ x, h x ∂μ := by
    intro h hh hint
    rw [integral_pos_iff_support_of_nonneg (fun x => (hh x).le) hint]
    have : Function.support h = Set.univ := by
      ext x; simp [Function.mem_support, (hh x).ne']
    rw [this]; simp [measure_univ]
  have ipos_β : ∀ {h : β → ℝ}, (∀ x, 0 < h x) → Integrable h ν → 0 < ∫ x, h x ∂ν := by
    intro h hh hint
    rw [integral_pos_iff_support_of_nonneg (fun x => (hh x).le) hint]
    have : Function.support h = Set.univ := by
      ext x; simp [Function.mem_support, (hh x).ne']
    rw [this]; simp [measure_univ]
  -- Abbreviations.
  set g₁ : α → ℝ := fun x ↦ ∫ y, f (x, y) ∂ν with hg₁
  set m : β → ℝ := fun y ↦ ∫ x, f (x, y) ∂μ with hm
  set M : ℝ := ∫ x, g₁ x ∂μ with hMdef
  have hg₁_pos : ∀ x, 0 < g₁ x := fun x => by
    rw [hg₁]; exact ipos_β (fun y => hf_pos _) (hfx_int x)
  have hfprodleft : ∀ᵐ y ∂ν, Integrable (fun x ↦ f (x, y)) μ := by
    have := hf_int.prod_left_ae (μ := μ) (ν := ν); simpa using this
  have hm_pos : ∀ᵐ y ∂ν, 0 < m y := by
    filter_upwards [hfprodleft] with y hy
    exact ipos_α (fun x => hf_pos _) hy
  have hM_pos : 0 < M := by
    rw [hMdef]; exact ipos_α hg₁_pos (by
      simpa [hg₁] using hf_int.integral_prod_left)
  have hM_eq : M = ∫ y, m y ∂ν := by
    rw [hMdef, hg₁, hm]
    exact integral_integral_swap (f := fun x y => f (x, y)) (by exact hf_int)
  -- Pointwise-in-x inequality.
  have hpt : ∀ x, g₁ x * Real.log (g₁ x) - g₁ x * Real.log M
      ≤ ∫ y, (f (x, y) * Real.log (f (x, y)) - f (x, y) * Real.log (m y)) ∂ν := by
    intro x
    set A : ℝ := g₁ x with hA
    have hA_pos : 0 < A := hg₁_pos x
    have hgibbs_ae : 0 ≤ᵐ[ν] fun y =>
        f (x, y) * Real.log (f (x, y))
          - f (x, y) * (Real.log A + Real.log (m y) - Real.log M)
          - (f (x, y) - A * m y / M) := by
      filter_upwards [hm_pos] with y hmy
      have hb_pos : 0 < A * m y / M := by positivity
      have hg := scalar_gibbs (hf_pos (x, y)).le hb_pos
      have hlogb : Real.log (A * m y / M)
          = Real.log A + Real.log (m y) - Real.log M := by
        rw [Real.log_div (by positivity) (ne_of_gt hM_pos), Real.log_mul (ne_of_gt hA_pos)
          (ne_of_gt hmy)]
      rw [hlogb] at hg
      show 0 ≤ f (x, y) * Real.log (f (x, y))
          - f (x, y) * (Real.log A + Real.log (m y) - Real.log M)
          - (f (x, y) - A * m y / M)
      linarith [hg]
    have hint_b : Integrable (fun y => A * m y / M) ν := by
      have : (fun y => A * m y / M) = fun y => (A / M) * m y := by funext y; ring
      rw [this]; exact hm_int.const_mul (A / M)
    have hfx_logm_int' : Integrable (fun y => f (x, y) * Real.log (m y)) ν := by
      have := hfx_logm_int x; rw [hm]; exact this
    have hint_flogA : Integrable (fun y => f (x, y) * Real.log A) ν :=
      (hfx_int x).mul_const _
    have hint_flogM : Integrable (fun y => f (x, y) * Real.log M) ν :=
      (hfx_int x).mul_const _
    have hint_bracket : Integrable
        (fun y => f (x, y) * (Real.log A + Real.log (m y) - Real.log M)) ν := by
      have hexp : (fun y => f (x, y) * (Real.log A + Real.log (m y) - Real.log M))
          = fun y => f (x, y) * Real.log A + f (x, y) * Real.log (m y)
              - f (x, y) * Real.log M := by funext y; ring
      rw [hexp]
      exact (hint_flogA.add (hfx_logm_int')).sub hint_flogM
    have hge0 : 0 ≤ ∫ y, (f (x, y) * Real.log (f (x, y))
          - f (x, y) * (Real.log A + Real.log (m y) - Real.log M)
          - (f (x, y) - A * m y / M)) ∂ν :=
      integral_nonneg_of_ae hgibbs_ae
    have hf_int_eq : (∫ y, f (x, y) ∂ν) = A := by rw [hA, hg₁]
    have hb_int_eq : (∫ y, A * m y / M ∂ν) = A := by
      have : (fun y => A * m y / M) = fun y => (A / M) * m y := by funext y; ring
      rw [this, integral_const_mul, ← hM_eq]; field_simp
    have hsplit : (∫ y, (f (x, y) * Real.log (f (x, y))
          - f (x, y) * (Real.log A + Real.log (m y) - Real.log M)
          - (f (x, y) - A * m y / M)) ∂ν)
        = (∫ y, (f (x, y) * Real.log (f (x, y))
            - f (x, y) * Real.log (m y)) ∂ν)
          - (A * Real.log A - A * Real.log M) := by
      have hbracket_int : (∫ y, f (x, y) * (Real.log A + Real.log (m y) - Real.log M) ∂ν)
          = (∫ y, f (x, y) * Real.log A ∂ν) + (∫ y, f (x, y) * Real.log (m y) ∂ν)
            - (∫ y, f (x, y) * Real.log M ∂ν) := by
        have hexp : (fun y => f (x, y) * (Real.log A + Real.log (m y) - Real.log M))
            = fun y => (f (x, y) * Real.log A + f (x, y) * Real.log (m y))
                - f (x, y) * Real.log M := by funext y; ring
        calc (∫ y, f (x, y) * (Real.log A + Real.log (m y) - Real.log M) ∂ν)
            = ∫ y, ((f (x, y) * Real.log A + f (x, y) * Real.log (m y))
                - f (x, y) * Real.log M) ∂ν := by rw [hexp]
          _ = (∫ y, (f (x, y) * Real.log A + f (x, y) * Real.log (m y)) ∂ν)
                - (∫ y, f (x, y) * Real.log M ∂ν) :=
              integral_sub (hint_flogA.add (hfx_logm_int')) hint_flogM
          _ = (∫ y, f (x, y) * Real.log A ∂ν) + (∫ y, f (x, y) * Real.log (m y) ∂ν)
                - (∫ y, f (x, y) * Real.log M ∂ν) := by
              rw [integral_add hint_flogA (hfx_logm_int')]
      calc (∫ y, (f (x, y) * Real.log (f (x, y))
              - f (x, y) * (Real.log A + Real.log (m y) - Real.log M)
              - (f (x, y) - A * m y / M)) ∂ν)
          = (∫ y, (f (x, y) * Real.log (f (x, y))
              - f (x, y) * (Real.log A + Real.log (m y) - Real.log M)) ∂ν)
            - (∫ y, (f (x, y) - A * m y / M) ∂ν) :=
            integral_sub ((hfx_logf_int x).sub' hint_bracket) ((hfx_int x).sub' hint_b)
        _ = ((∫ y, f (x, y) * Real.log (f (x, y)) ∂ν)
              - (∫ y, f (x, y) * (Real.log A + Real.log (m y) - Real.log M) ∂ν))
            - ((∫ y, f (x, y) ∂ν) - (∫ y, A * m y / M ∂ν)) := by
            rw [integral_sub (hfx_logf_int x) hint_bracket,
              integral_sub (hfx_int x) hint_b]
        _ = (∫ y, (f (x, y) * Real.log (f (x, y))
              - f (x, y) * Real.log (m y)) ∂ν)
            - (A * Real.log A - A * Real.log M) := by
            have hflogA : (∫ y, f (x, y) * Real.log A ∂ν) = A * Real.log A := by
              rw [integral_mul_const, hf_int_eq]
            have hflogM : (∫ y, f (x, y) * Real.log M ∂ν) = A * Real.log M := by
              rw [integral_mul_const, hf_int_eq]
            rw [hbracket_int, hb_int_eq, hflogA, hflogM,
              integral_sub (hfx_logf_int x) (hfx_logm_int')]
            ring
    rw [hsplit] at hge0
    linarith [hge0]
  -- LHS = ∫_x (g₁ log g₁ - g₁ log M) dμ.
  have hLHS : ( (∫ x, g₁ x * Real.log (g₁ x) ∂μ)
        - (∫ x, g₁ x ∂μ) * Real.log (∫ x, g₁ x ∂μ) )
      = ∫ x, (g₁ x * Real.log (g₁ x) - g₁ x * Real.log M) ∂μ := by
    rw [← hMdef]
    have hint1 : Integrable (fun x => g₁ x * Real.log (g₁ x)) μ := by simpa [hg₁] using hg1log_int
    have hint2 : Integrable (fun x => g₁ x * Real.log M) μ := by
      have : Integrable g₁ μ := by simpa [hg₁] using hf_int.integral_prod_left
      exact this.mul_const _
    rw [integral_sub hint1 hint2, integral_mul_const]
  -- a.e.-y integrabilities of the inner-x fibres.
  have hae_flogf : ∀ᵐ y ∂ν, Integrable (fun x ↦ f (x, y) * Real.log (f (x, y))) μ := by
    have := hflog_int.prod_left_ae (μ := μ) (ν := ν); simpa using this
  have hae_fy : ∀ᵐ y ∂ν, Integrable (fun x ↦ f (x, y)) μ := hfprodleft
  -- RHS = ∫_x ∫_y (f log f - f log m) dν dμ  (per-y rewrite + Fubini).
  have hRHS : ( ∫ y, ( (∫ x, f (x, y) * Real.log (f (x, y)) ∂μ)
              - (∫ x, f (x, y) ∂μ) * Real.log (∫ x, f (x, y) ∂μ) ) ∂ν )
      = ∫ x, (∫ y, (f (x, y) * Real.log (f (x, y)) - f (x, y) * Real.log (m y)) ∂ν) ∂μ := by
    have hper_y : ∀ᵐ y ∂ν, ( (∫ x, f (x, y) * Real.log (f (x, y)) ∂μ)
          - (∫ x, f (x, y) ∂μ) * Real.log (∫ x, f (x, y) ∂μ) )
        = ∫ x, (f (x, y) * Real.log (f (x, y)) - f (x, y) * Real.log (m y)) ∂μ := by
      filter_upwards [hae_flogf, hae_fy] with y hflogf hfy
      have hint_flogm : Integrable (fun x => f (x, y) * Real.log (m y)) μ := hfy.mul_const _
      rw [integral_sub hflogf hint_flogm, integral_mul_const]
    rw [integral_congr_ae hper_y]
    refine (integral_integral_swap (f := fun x y =>
        f (x, y) * Real.log (f (x, y)) - f (x, y) * Real.log (m y)) ?_).symm
    have h1 : Integrable (fun p : α × β => f p * Real.log (f p)) (μ.prod ν) := hflog_int
    have h2 : Integrable (fun p : α × β => f p * Real.log (m p.2)) (μ.prod ν) := by
      simpa [hm] using hfm_prod_int
    exact h1.sub h2
  have hLHS_int : Integrable (fun x => g₁ x * Real.log (g₁ x) - g₁ x * Real.log M) μ := by
    have hint1 : Integrable (fun x => g₁ x * Real.log (g₁ x)) μ := by simpa [hg₁] using hg1log_int
    have hint2 : Integrable (fun x => g₁ x * Real.log M) μ := by
      have : Integrable g₁ μ := by simpa [hg₁] using hf_int.integral_prod_left
      exact this.mul_const _
    exact hint1.sub hint2
  rw [show (∫ x, (∫ y, f (x, y) ∂ν) * Real.log (∫ y, f (x, y) ∂ν) ∂μ)
        - (∫ x, (∫ y, f (x, y) ∂ν) ∂μ) * Real.log (∫ x, (∫ y, f (x, y) ∂ν) ∂μ)
      = (∫ x, g₁ x * Real.log (g₁ x) ∂μ)
        - (∫ x, g₁ x ∂μ) * Real.log (∫ x, g₁ x ∂μ) from rfl]
  rw [hLHS, hRHS]
  exact integral_mono_ae hLHS_int h_inner_x_int (ae_of_all _ hpt)

#print axioms solution
