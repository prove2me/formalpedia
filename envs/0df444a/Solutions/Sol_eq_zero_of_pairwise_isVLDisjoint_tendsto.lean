-- Prove2me | solution 1 for eq_zero_of_pairwise_isVLDisjoint_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:18:55.942564+00:00
-- url     : https://prove2.me/submissions/64d53083-0192-4fed-b8da-5b7c3be3188b

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Normed
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Theorems.Thm_abs_add_of_isVLDisjoint

set_option autoImplicit true
@[expose] public section
public section
open scoped Topology
open Filter Finset
theorem _root_.solution {Y : Type*}
    [NormedAddCommGroup Y] [Lattice Y] [IsOrderedAddMonoid Y]
    [NormedVectorLattice Y] {u : ℕ → Y} {x : Y}
    (hdisj : Pairwise fun i j => IsVLDisjoint (u i) (u j))
    (hlim : Tendsto u atTop (𝓝 x)) : x = 0 := by
  have habs_bound : ∀ n m, n ≠ m → |u n| ≤ |u n - u m| := by
    intro n m hnm
    have hdnm : IsVLDisjoint (u n) (-u m) := by
      change |u n| ⊓ |-u m| = 0
      rw [abs_neg]; exact hdisj hnm
    rw [sub_eq_add_neg, abs_add_of_isVLDisjoint hdnm, abs_neg]
    exact le_add_of_nonneg_right (abs_nonneg _)
  have hnorm_bound : ∀ n m, n ≠ m → ‖u n‖ ≤ ‖u n - u m‖ :=
    fun n m hnm => norm_le_norm_of_abs_le_abs (habs_bound n m hnm)
  have hnorm_limit : ∀ n, ‖u n‖ ≤ ‖u n - x‖ := by
    intro n
    have hrhs : Tendsto (fun m => ‖u n - u m‖) atTop (𝓝 ‖u n - x‖) :=
      (continuous_norm.tendsto _).comp (hlim.const_sub _)
    refine ge_of_tendsto hrhs ?_
    filter_upwards [eventually_ne_atTop n] with m hm
    exact hnorm_bound n m hm.symm
  have hlhs_tendsto : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖x‖) :=
    (continuous_norm.tendsto _).comp hlim
  have hrhs_zero : Tendsto (fun n => ‖u n - x‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => u n - x) atTop (𝓝 0) := by
      simpa using hlim.sub_const x
    simpa only [Function.comp_def, norm_zero] using (continuous_norm.tendsto (0 : Y)).comp h1
  have hxnn : ‖x‖ ≤ 0 :=
    le_of_tendsto_of_tendsto' hlhs_tendsto hrhs_zero hnorm_limit
  exact norm_le_zero_iff.mp hxnn
