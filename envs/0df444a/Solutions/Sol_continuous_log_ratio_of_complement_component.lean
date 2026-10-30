-- Prove2me | solution 1 for continuous_log_ratio_of_complement_component
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T02:04:56.504262+00:00
-- url     : https://prove2.me/submissions/baabec18-b38f-44a3-b6f3-fbb67b9b684f

import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting

open Set Function Topology unitInterval

/-- A continuous nonzero homotopy starting at one has a continuous logarithm at its endpoint. -/
lemma continuous_log_of_homotopy_from_one {A : Type} [TopologicalSpace A]
    (H : C(I × A, {z : ℂ // z ≠ 0}))
    (h0 : ∀ x, (H (0, x)).1 = 1) :
    ∃ f : C(A, ℂ), ∀ x, Complex.exp (f x) = (H (1, x)).1 := by
  let f₀ : C(A, ℂ) := ContinuousMap.const A 0
  have hstart : ∀ x, H (0, x) = (⟨Complex.exp (f₀ x), Complex.exp_ne_zero _⟩ : {z : ℂ // z ≠ 0}) := by
    intro x
    apply Subtype.ext
    simpa [f₀] using h0 x
  let L := Complex.isCoveringMap_exp.liftHomotopy H f₀ hstart
  let j : C(A, I × A) := (ContinuousMap.const A 1).prodMk (ContinuousMap.id A)
  refine ⟨L.comp j, ?_⟩
  intro x
  have hlift := congr_fun (Complex.isCoveringMap_exp.liftHomotopy_lifts H f₀ hstart) (1, x)
  exact congrArg Subtype.val hlift


/-- A path from a to b avoiding K supplies a continuous logarithm of
z ↦ (z-a)/(z-b) on K. -/
lemma continuous_log_ratio_of_path_avoiding
    (K : Set ℂ) (a b : ℂ) (γ : Path a b) (hγ : ∀ t : I, γ t ∉ K) :
    ∃ f : ℂ → ℂ, ContinuousOn f K ∧
      EqOn (fun z => Complex.exp (f z)) (fun z => (z - a) / (z - b)) K := by
  classical
  have haK : a ∉ K := by simpa only [γ.source] using hγ 0
  have hnum (z : K) : z.1 - a ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    apply haK
    simpa only [h] using z.2
  have hden (t : I) (z : K) : z.1 - γ t ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    apply hγ t
    simpa only [h] using z.2
  let H : C(I × K, {z : ℂ // z ≠ 0}) :=
    ⟨fun q => ⟨(q.2.1 - a) / (q.2.1 - γ q.1), div_ne_zero (hnum q.2) (hden q.1 q.2)⟩,
      ((continuous_subtype_val.comp continuous_snd).sub continuous_const).div
        ((continuous_subtype_val.comp continuous_snd).sub (γ.continuous.comp continuous_fst))
        (fun q => hden q.1 q.2) |>.subtype_mk _⟩
  have h0 : ∀ z : K, (H (0, z)).1 = 1 := by
    intro z
    change (z.1 - a) / (z.1 - γ 0) = 1
    rw [γ.source]
    exact div_self (hnum z)
  obtain ⟨F, hF⟩ := continuous_log_of_homotopy_from_one H h0
  let f : ℂ → ℂ := fun z => if hz : z ∈ K then F ⟨z, hz⟩ else 0
  have hfc : ContinuousOn f K := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : K.domRestrict f = F := by
      funext z
      simp [f]
    rw [heq]
    exact F.continuous
  refine ⟨f, hfc, ?_⟩
  intro z hz
  have h := hF ⟨z, hz⟩
  change Complex.exp (f z) = (z - a) / (z - b)
  simpa [f, H, γ.target, hz] using h


/-- If two points are in one component of the complement of a closed planar set,
their ratio map has a continuous logarithm on the set. -/
theorem solution
    (K : Set ℂ) (hK : IsClosed K) (a b : ℂ)
    (hab : b ∈ connectedComponentIn Kᶜ a) :
    ∃ f : ℂ → ℂ, ContinuousOn f K ∧
      EqOn (fun z => Complex.exp (f z)) (fun z => (z - a) / (z - b)) K := by
  have ha : a ∈ Kᶜ := connectedComponentIn_nonempty_iff.mp ⟨b, hab⟩
  let C := connectedComponentIn Kᶜ a
  have hCopen : IsOpen C := hK.isOpen_compl.connectedComponentIn
  have hCconn : IsConnected C := isConnected_connectedComponentIn_iff.mpr ha
  have hCpath : IsPathConnected C := hCopen.isConnected_iff_isPathConnected.mp hCconn
  have haC : a ∈ C := mem_connectedComponentIn ha
  obtain ⟨γ, hγ⟩ := hCpath.joinedIn a haC b hab
  apply continuous_log_ratio_of_path_avoiding K a b γ
  intro t
  exact connectedComponentIn_subset Kᶜ a (hγ t)

#print axioms solution
