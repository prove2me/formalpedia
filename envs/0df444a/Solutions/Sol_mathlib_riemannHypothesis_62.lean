-- Prove2me | solution 62 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:30:26.293694+00:00
-- url     : https://prove2.me/submissions/bd8b0fe2-6fd3-45c3-b268-611ac42a362a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_MasulloRH_regularized_rhs_analytic
import Theorems.Thm_MasulloRH_regularized_initial_identity
import Theorems.Thm_MasulloRH_derivative_identity_continuation
import Theorems.Thm_MasulloRH_logDeriv_analytic_of_local_ode
import Mathlib.Tactic.Linarith
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Meromorphic.Order
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line

-- Step 1: `MasulloRH.regularized_initial_identity` implies `MasulloRH.logDeriv_on_strip_complement` (accepted reduction of `MasulloRH.logDeriv_on_strip_complement`).
section

set_option autoImplicit false

open MasulloRH Set Filter
open scoped Topology

/-- Continue an analytic derivative identity, then use local analytic ODE uniqueness. -/
theorem MasulloRH.logDeriv_on_strip_complement (α : ℝ) (hα : 0 < α) (hαsmall : α < 1 / 2)
    (s : ℂ) (hs : InTraceContinuationDomain α s) :
    AnalyticAt ℂ zetaLogDeriv s := by
  have hhol := regularized_rhs_analytic α hα hαsmall
  have hinit := regularized_initial_identity α hα hαsmall
  apply logDeriv_analytic_of_local_ode s hs.2 (regularizedTraceRHS α) (hhol s hs)
  have hopen : IsOpen {z : ℂ | InTraceContinuationDomain α z} := by
    change IsOpen ({z : ℂ | 1 / 2 + α < z.re} ∩ {z : ℂ | z ≠ 1})
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      isOpen_compl_singleton
  filter_upwards [hopen.mem_nhds hs] with z hz
  exact derivative_identity_continuation α hα hαsmall hhol hinit z hz

end

-- Step 2: `MasulloRH.logDeriv_on_strip_complement` implies `MasulloRH.logDeriv_analytic_right` (accepted reduction of `MasulloRH.logDeriv_analytic_right`).
section

set_option autoImplicit false

open MasulloRH

/-- Any point right of the critical line lies beyond a smaller positive strip. -/
theorem MasulloRH.logDeriv_analytic_right (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) :
    AnalyticAt ℂ (fun z : ℂ => deriv riemannZeta z / riemannZeta z) s := by
  let α : ℝ := min ((s.re - 1 / 2) / 2) (1 / 4)
  have hα : 0 < α := by
    dsimp [α]
    exact lt_min (by linarith) (by norm_num)
  have hsmall : α < 1 / 2 := by
    have hle : α ≤ 1 / 4 := min_le_right _ _
    linarith
  have hdomain : InTraceContinuationDomain α s := by
    refine ⟨?_, hs_one⟩
    have hle : α ≤ (s.re - 1 / 2) / 2 := min_le_left _ _
    linarith
  exact logDeriv_on_strip_complement α hα hsmall s hdomain

end

-- Step 3: `MasulloRH.logDeriv_analytic_right` implies `MasulloRH.zero_free_right` (accepted reduction of `MasulloRH.zero_free_right`).
section

set_option autoImplicit false

open Filter
open scoped Topology

/-- A zero would give the logarithmic derivative meromorphic order `-1`,
contradicting the imported analyticity assertion. -/
theorem MasulloRH.zero_free_right (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs_one : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  have ha : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs_one
  have hpos : 0 < meromorphicOrderAt riemannZeta s := by
    apply (tendsto_zero_iff_meromorphicOrderAt_pos ha.meromorphicAt).mp
    simpa only [hz] using ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ z in 𝓝[≠] s, riemannZeta z ≠ 0 := by
    have hd := (isClosed_and_discrete_iff.mp
      ⟨isClosed_riemannZetaZeros, isDiscrete_riemannZetaZeros⟩) s
    change riemannZetaZerosᶜ ∈ 𝓝[≠] s
    exact Filter.disjoint_principal_right.mp hd
  have hfinite : meromorphicOrderAt riemannZeta s ≠ ⊤ := by
    intro htop
    obtain ⟨z, hne, heq⟩ := (hnear.and (meromorphicOrderAt_eq_top_iff.mp htop)).exists
    exact hne heq
  have hpole := meromorphicOrderAt_logDeriv_eq_neg_one ha.meromorphicAt
    (ne_of_gt hpos) hfinite
  have hnonneg := (MasulloRH.logDeriv_analytic_right s hs hs_one).meromorphicOrderAt_nonneg
  change 0 ≤ meromorphicOrderAt (logDeriv riemannZeta) s at hnonneg
  rw [hpole] at hnonneg
  change ((0 : ℤ) : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ) at hnonneg
  have hbad : (0 : ℤ) ≤ -1 := WithTop.coe_le_coe.mp hnonneg
  norm_num at hbad

end

-- Step 4: `MasulloRH.zero_free_right` implies `RiemannHypothesis` (accepted reduction of `mathlib_riemannHypothesis`).
section

theorem solution : RiemannHypothesis := by
  have hright : ∀ s : ℂ, (1 / 2 : ℝ) < s.re → s ≠ 1 → riemannZeta s ≠ 0 :=
    fun s hs hs1 => MasulloRH.zero_free_right s hs hs1
  refine riemannHypothesis_iff_zeros_in_strip_on_line.mpr (fun s hz h0 h1 => ?_)
  have hs1 : s ≠ 1 := fun h => by rw [h] at h1; norm_num at h1
  rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
  · exfalso
    have hneg : ∀ n : ℕ, s ≠ -(n : ℂ) := fun n h => by
      have hre := congrArg Complex.re h
      simp at hre
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hfe := riemannZeta_one_sub hneg hs1
    rw [hz, mul_zero] at hfe
    have hre : (1 / 2 : ℝ) < (1 - s).re := by simp; linarith
    have h1s : (1 - s) ≠ 1 := fun h => by
      have hre' := congrArg Complex.re h
      simp at hre'
      linarith
    exact hright (1 - s) hre h1s hfe
  · exact heq
  · exact absurd hz (hright s hgt hs1)

end
