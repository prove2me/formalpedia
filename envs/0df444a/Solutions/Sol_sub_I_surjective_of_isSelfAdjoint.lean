-- Prove2me | solution 1 for sub_I_surjective_of_isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:42.813227+00:00
-- url     : https://prove2.me/submissions/cd2dd56d-1a35-4dfa-957d-e96c8b47bd06

import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Definitions.Def_Spectral_Cayley_Basic
section
open scoped LinearPMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
private theorem isClosed_range_minusI (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    IsClosed ((LinearMap.range (minusI A) : Submodule ℂ E) : Set E) := by
  rw [← isSeqClosed_iff_isClosed]
  intro y y₀ hy hylim
  choose x hx using hy
  have hyCauchy : CauchySeq y := hylim.cauchySeq
  have hdist (m n : ℕ) :
      dist ((x m : A.domain) : E) ((x n : A.domain) : E) ≤ dist (y m) (y n) := by
    rw [dist_eq_norm, dist_eq_norm]
    calc
      ‖(((x m - x n : A.domain) : E))‖ ≤ ‖minusI A (x m - x n)‖ :=
        norm_le_minusI A hA (x m - x n)
      _ = ‖y m - y n‖ := by rw [map_sub, hx m, hx n]
  have hxCauchy : CauchySeq (fun n => ((x n : A.domain) : E)) := by
    rw [Metric.cauchySeq_iff] at hyCauchy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hyCauchy ε hε
    exact ⟨N, fun m hm n hn => (hdist m n).trans_lt (hN m hm n hn)⟩
  obtain ⟨x₀, hxlim⟩ := cauchySeq_tendsto_of_complete hxCauchy
  have hIlim :
      Filter.Tendsto (fun n => Complex.I • ((x n : A.domain) : E)) Filter.atTop
        (nhds (Complex.I • x₀)) :=
    tendsto_const_nhds.smul hxlim
  have hAlim : Filter.Tendsto (fun n => A (x n)) Filter.atTop
      (nhds (y₀ + Complex.I • x₀)) := by
    have heq : (fun n => A (x n)) =
        (fun n => y n + Complex.I • ((x n : A.domain) : E)) := by
      funext n
      rw [← hx n]
      change A (x n) = (A (x n) - Complex.I • ((x n : A.domain) : E)) +
        Complex.I • ((x n : A.domain) : E)
      rw [sub_add_cancel]
    rw [heq]
    exact hylim.add hIlim
  have hgraph : (x₀, y₀ + Complex.I • x₀) ∈ A.graph := by
    apply hA.isClosed.mem_of_tendsto (hxlim.prodMk_nhds hAlim)
    exact Filter.Eventually.of_forall fun n => A.mem_graph (x n)
  rw [LinearPMap.mem_graph_iff] at hgraph
  obtain ⟨x₀', hx₀', hAx₀'⟩ := hgraph
  refine ⟨x₀', ?_⟩
  change A x₀' - Complex.I • (x₀' : E) = y₀
  rw [hAx₀', hx₀', add_sub_cancel_right]
private theorem orthogonal_range_minusI_eq_bot (A : E →ₗ.[ℂ] E)
    (hA : IsSelfAdjoint A) : (LinearMap.range (minusI A))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  have hyOrth := (LinearMap.range (minusI A)).mem_orthogonal' y |>.mp hy
  have hwitness (x : A.domain) :
      inner ℂ ((-Complex.I) • y) (x : E) = inner ℂ y (A x) := by
    have hzero := hyOrth (minusI A x) (LinearMap.mem_range.mpr ⟨x, rfl⟩)
    change inner ℂ y (A x - Complex.I • (x : E)) = 0 at hzero
    rw [inner_sub_right, inner_smul_right] at hzero
    rw [neg_smul, inner_neg_left, inner_smul_left, Complex.conj_I]
    linear_combination -hzero
  have hyAdj : y ∈ A†.domain :=
    LinearPMap.mem_adjoint_domain_of_exists y ⟨(-Complex.I) • y, hwitness⟩
  have hyDom : y ∈ A.domain := by
    rw [← LinearPMap.isSelfAdjoint_def.mp hA]
    exact hyAdj
  let yDom : A.domain := ⟨y, hyDom⟩
  have hAy : A yDom = (-Complex.I) • y := by
    apply hA.dense_domain.eq_of_inner_left ℂ
    intro x hx
    let xDom : A.domain := ⟨x, hx⟩
    calc
      inner ℂ (A yDom) x = inner ℂ y (A xDom) := formalSelfAdjoint A hA yDom xDom
      _ = inner ℂ ((-Complex.I) • y) x := (hwitness xDom).symm
  have hplus : plusI A yDom = 0 := by
    change A yDom + Complex.I • y = 0
    rw [hAy, neg_smul, neg_add_cancel]
  have hynorm : ‖y‖ ≤ 0 := by
    simpa only [hplus, norm_zero] using norm_le_plusI A hA yDom
  exact norm_eq_zero.mp (le_antisymm hynorm (norm_nonneg _))
private theorem minusI_surjective (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    Function.Surjective (minusI A) := by
  let K : Submodule ℂ E := LinearMap.range (minusI A)
  have hclosed : IsClosed (K : Set E) := isClosed_range_minusI A hA
  have horth : Kᗮ = ⊥ := orthogonal_range_minusI_eq_bot A hA
  have hclosure : K.topologicalClosure = ⊤ := by
    rw [← K.orthogonal_orthogonal_eq_closure, horth, Submodule.bot_orthogonal_eq_top]
  have htop : K = ⊤ := by
    calc
      K = K.topologicalClosure := hclosed.submodule_topologicalClosure_eq.symm
      _ = ⊤ := hclosure
  intro y
  apply LinearMap.mem_range.mp
  change y ∈ K
  rw [htop]
  exact Submodule.mem_top
end

set_option autoImplicit false
open scoped LinearPMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    Function.Surjective (fun x : A.domain => A x - Complex.I • (x : E)) := by
  exact minusI_surjective A hA
