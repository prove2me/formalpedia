-- Prove2me | solution 1 for planar_arc_attachment_different_components_count
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T02:33:19.367519+00:00
-- url     : https://prove2.me/submissions/9b7c145c-f2d5-40ef-9f84-8cb7d08681fe

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Separation.Lemmas
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Piecewise
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.MetricSpace.Bounded
import Definitions.Def_Schoenflies_Bounded
import Definitions.Def_Schoenflies_Graph_OuterFace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Separation.Regular
import Mathlib.Data.Set.Card
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_Schoenflies_SquareCycle

open Set

/-- Continuous functions on closed sets meeting in a singleton can be glued after
translating the second function to agree at the shared point. -/
lemma glue_translate_singleton {X : Type} [TopologicalSpace X]
    (S T : Set X) (p : X) (f g : X → ℂ)
    (hS : IsClosed S) (hT : IsClosed T) (hint : S ∩ T = {p})
    (hf : ContinuousOn f S) (hg : ContinuousOn g T) :
    ∃ k : X → ℂ, ContinuousOn k (S ∪ T) ∧ EqOn k f S ∧
      EqOn k (fun x => g x + (f p - g p)) T := by
  classical
  let k := S.piecewise f (fun x => g x + (f p - g p))
  have hks : EqOn k f S := by
    intro x hx
    simp [k, hx]
  have hkt : EqOn k (fun x => g x + (f p - g p)) T := by
    intro x hx
    by_cases hxS : x ∈ S
    · have hxp : x = p := by
        have hxint : x ∈ S ∩ T := ⟨hxS, hx⟩
        rw [hint] at hxint
        exact Set.mem_singleton_iff.mp hxint
      subst x
      simp [k, hxS]
    · simp [k, hxS]
  refine ⟨k, ?_, hks, hkt⟩
  have hkcS : ContinuousOn k S := hf.congr hks
  have hkcT : ContinuousOn k T := (hg.add continuousOn_const).congr hkt
  exact hkcS.union_of_isClosed hkcT hS hT

/-- Compatible complex logarithms on singleton-overlapping closed sets glue after a constant
adjustment of one branch. -/
lemma glue_exp_lifts_singleton {X : Type} [TopologicalSpace X]
    (S T : Set X) (p : X) (f g : X → ℂ)
    (hS : IsClosed S) (hT : IsClosed T) (hint : S ∩ T = {p})
    (hf : ContinuousOn f S) (hg : ContinuousOn g T)
    (heq : Complex.exp (f p) = Complex.exp (g p)) :
    ∃ k : X → ℂ, ContinuousOn k (S ∪ T) ∧
      EqOn (fun x => Complex.exp (k x)) (fun x => Complex.exp (f x)) S ∧
      EqOn (fun x => Complex.exp (k x)) (fun x => Complex.exp (g x)) T := by
  obtain ⟨k, hkc, hks, hkt⟩ := glue_translate_singleton S T p f g hS hT hint hf hg
  refine ⟨k, hkc, ?_, ?_⟩
  · intro x hx
    change Complex.exp (k x) = Complex.exp (f x)
    rw [hks hx]
  · intro x hx
    change Complex.exp (k x) = Complex.exp (g x)
    rw [hkt hx, Complex.exp_add, Complex.exp_sub, heq]
    simp [Complex.exp_ne_zero]


/-- Janiszewski's singleton-intersection conclusion follows from a characterization
of complement components by continuous logarithms of the indicated ratio. -/
lemma singleton_separation_of_log_characterization
    (a b : ℂ)
    (hchar : ∀ K : Set ℂ, IsCompact K → a ∉ K → b ∉ K →
      (b ∈ connectedComponentIn Kᶜ a ↔
        ∃ f : ℂ → ℂ, ContinuousOn f K ∧
          EqOn (fun z => Complex.exp (f z)) (fun z => (z - a) / (z - b)) K))
    (S T : Set ℂ) (p : ℂ) (hS : IsCompact S) (hT : IsCompact T)
    (hint : S ∩ T = {p}) (ha : a ∉ S ∪ T) (hb : b ∉ S ∪ T)
    (haS : b ∈ connectedComponentIn Sᶜ a)
    (haT : b ∈ connectedComponentIn Tᶜ a) :
    b ∈ connectedComponentIn (S ∪ T)ᶜ a := by
  have hSa : a ∉ S := fun h => ha (Or.inl h)
  have hTa : a ∉ T := fun h => ha (Or.inr h)
  have hSb : b ∉ S := fun h => hb (Or.inl h)
  have hTb : b ∉ T := fun h => hb (Or.inr h)
  obtain ⟨f, hfc, hfe⟩ := (hchar S hS hSa hSb).mp haS
  obtain ⟨g, hgc, hge⟩ := (hchar T hT hTa hTb).mp haT
  have hp : p ∈ S ∩ T := by rw [hint]; simp
  have heq : Complex.exp (f p) = Complex.exp (g p) :=
    (hfe hp.1).trans (hge hp.2).symm
  obtain ⟨k, hkc, hkS, hkT⟩ :=
    glue_exp_lifts_singleton S T p f g hS.isClosed hT.isClosed hint hfc hgc heq
  apply (hchar (S ∪ T) (hS.union hT) ha hb).mpr
  refine ⟨k, hkc, ?_⟩
  intro z hz
  rcases hz with hz | hz
  · exact (hkS hz).trans (hfe hz)
  · exact (hkT hz).trans (hge hz)


/-- The fiber of the complex exponential over one is countable. -/
lemma complex_exp_one_fiber_countable : {z : ℂ | Complex.exp z = 1}.Countable := by
  apply (Set.countable_range (fun n : ℤ => (n : ℂ) * (2 * Real.pi * Complex.I))).mono
  intro z hz
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hz
  exact ⟨n, hn.symm⟩

/-- Two continuous lifts with equal exponentials differ by a constant on a preconnected set. -/
lemma exp_lifts_diff_constant_on_preconnected {X : Type} [TopologicalSpace X]
    (W : Set X) (f g : X → ℂ) (hW : IsPreconnected W)
    (hf : ContinuousOn f W) (hg : ContinuousOn g W)
    (heq : EqOn (fun x => Complex.exp (f x)) (fun x => Complex.exp (g x)) W)
    (p : X) (hp : p ∈ W) :
    ∀ x ∈ W, f x - g x = f p - g p := by
  let H : X → ℂ := fun x => f x - g x
  have hH : ContinuousOn H W := hf.sub hg
  have hconnected : IsPreconnected (H '' W) := hW.image H hH
  have hsubset : H '' W ⊆ {z : ℂ | Complex.exp z = 1} := by
    rintro z ⟨x, hx, rfl⟩
    change Complex.exp (f x - g x) = 1
    exact Complex.exp_eq_exp_iff_exp_sub_eq_one.mp (heq hx)
  have hsub : (H '' W).Subsingleton :=
    complex_exp_one_fiber_countable.isTotallyDisconnected _ hsubset hconnected
  intro x hx
  exact hsub ⟨x, hx, rfl⟩ ⟨p, hp, rfl⟩

/-- Exponential lifts on closed sets with connected nonempty overlap glue after a
constant adjustment, retaining the original exponentials on each set. -/
lemma glue_exp_lifts_connected {X : Type} [TopologicalSpace X]
    (S T : Set X) (f g : X → ℂ) (hS : IsClosed S) (hT : IsClosed T)
    (hW : IsConnected (S ∩ T)) (hf : ContinuousOn f S) (hg : ContinuousOn g T)
    (heq : EqOn (fun x => Complex.exp (f x)) (fun x => Complex.exp (g x)) (S ∩ T)) :
    ∃ k : X → ℂ, ContinuousOn k (S ∪ T) ∧
      EqOn (fun x => Complex.exp (k x)) (fun x => Complex.exp (f x)) S ∧
      EqOn (fun x => Complex.exp (k x)) (fun x => Complex.exp (g x)) T := by
  classical
  obtain ⟨p, hp⟩ := hW.nonempty
  have hd := exp_lifts_diff_constant_on_preconnected (S ∩ T) f g hW.isPreconnected
    (hf.mono inter_subset_left) (hg.mono inter_subset_right) heq p hp
  let k := S.piecewise f (fun x => g x + (f p - g p))
  have hks : EqOn k f S := by
    intro x hx
    simp [k, hx]
  have hkt : EqOn k (fun x => g x + (f p - g p)) T := by
    intro x hx
    by_cases hxS : x ∈ S
    · have hdiff := hd x ⟨hxS, hx⟩
      have hmatch : f x = g x + (f p - g p) := by
        calc
          f x = (f x - g x) + g x := by abel
          _ = (f p - g p) + g x := by rw [hdiff]
          _ = g x + (f p - g p) := add_comm _ _
      simpa [k, hxS] using hmatch
    · simp [k, hxS]
  have hkcS : ContinuousOn k S := hf.congr hks
  have hkcT : ContinuousOn k T := (hg.add continuousOn_const).congr hkt
  have hkc : ContinuousOn k (S ∪ T) := hkcS.union_of_isClosed hkcT hS hT
  have heqp : Complex.exp (f p) = Complex.exp (g p) := heq hp
  refine ⟨k, hkc, ?_, ?_⟩
  · intro x hx
    change Complex.exp (k x) = Complex.exp (f x)
    rw [hks hx]
  · intro x hx
    change Complex.exp (k x) = Complex.exp (g x)
    rw [hkt hx, Complex.exp_add, Complex.exp_sub, heqp]
    simp [Complex.exp_ne_zero]


/-- Exponential lifts glue across any preconnected overlap, including the empty case. -/
lemma glue_exp_lifts_preconnected {X : Type} [TopologicalSpace X]
    (S T : Set X) (f g : X → ℂ) (hS : IsClosed S) (hT : IsClosed T)
    (hW : IsPreconnected (S ∩ T)) (hf : ContinuousOn f S) (hg : ContinuousOn g T)
    (heq : EqOn (fun x => Complex.exp (f x)) (fun x => Complex.exp (g x)) (S ∩ T)) :
    ∃ k : X → ℂ, ContinuousOn k (S ∪ T) ∧
      EqOn (fun x => Complex.exp (k x)) (fun x => Complex.exp (f x)) S ∧
      EqOn (fun x => Complex.exp (k x)) (fun x => Complex.exp (g x)) T := by
  classical
  by_cases hne : (S ∩ T).Nonempty
  · exact glue_exp_lifts_connected S T f g hS hT ⟨hne, hW⟩ hf hg heq
  · have hd : Disjoint S T := Set.disjoint_iff_inter_eq_empty.mpr
      (Set.not_nonempty_iff_eq_empty.mp hne)
    let k := S.piecewise f g
    have hks : EqOn k f S := by
      intro x hx
      simp [k, hx]
    have hkt : EqOn k g T := by
      intro x hx
      have hxS : x ∉ S := fun hs => Set.disjoint_left.mp hd hs hx
      simp [k, hxS]
    have hkc : ContinuousOn k (S ∪ T) :=
      (hf.congr hks).union_of_isClosed (hg.congr hkt) hS hT
    exact ⟨k, hkc, fun x hx => congrArg Complex.exp (hks hx),
      fun x hx => congrArg Complex.exp (hkt hx)⟩

/-- The compact planar Janiszewski principle follows from the logarithmic characterization
of complement components. The characterization is an explicit hypothesis. -/
lemma janiszewski_of_log_characterization
    (a b : ℂ)
    (hchar : ∀ K : Set ℂ, IsCompact K → a ∉ K → b ∉ K →
      (b ∈ connectedComponentIn Kᶜ a ↔
        ∃ f : ℂ → ℂ, ContinuousOn f K ∧
          EqOn (fun z => Complex.exp (f z)) (fun z => (z - a) / (z - b)) K))
    (S T : Set ℂ) (hS : IsCompact S) (hT : IsCompact T)
    (hST : IsPreconnected (S ∩ T)) (ha : a ∉ S ∪ T) (hb : b ∉ S ∪ T)
    (habS : b ∈ connectedComponentIn Sᶜ a)
    (habT : b ∈ connectedComponentIn Tᶜ a) :
    b ∈ connectedComponentIn (S ∪ T)ᶜ a := by
  have hSa : a ∉ S := fun h => ha (Or.inl h)
  have hTa : a ∉ T := fun h => ha (Or.inr h)
  have hSb : b ∉ S := fun h => hb (Or.inl h)
  have hTb : b ∉ T := fun h => hb (Or.inr h)
  obtain ⟨f, hfc, hfe⟩ := (hchar S hS hSa hSb).mp habS
  obtain ⟨g, hgc, hge⟩ := (hchar T hT hTa hTb).mp habT
  have heq : EqOn (fun z => Complex.exp (f z)) (fun z => Complex.exp (g z)) (S ∩ T) := by
    intro z hz
    exact (hfe hz.1).trans (hge hz.2).symm
  obtain ⟨k, hkc, hkS, hkT⟩ :=
    glue_exp_lifts_preconnected S T f g hS.isClosed hT.isClosed hST hfc hgc heq
  apply (hchar (S ∪ T) (hS.union hT) ha hb).mpr
  refine ⟨k, hkc, ?_⟩
  intro z hz
  rcases hz with hz | hz
  · exact (hkS hz).trans (hfe hz)
  · exact (hkT hz).trans (hge hz)

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
lemma continuous_log_ratio_of_same_component
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

/-- A map admitting a continuous logarithm has zero lift increment on any
closed loop in its domain. -/
lemma log_lift_increment_eq_zero_on_closed_loop
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (W : Set X) (hW : IsPreconnected W) (S : Set Y)
    (u v : X) (hu : u ∈ W) (hv : v ∈ W)
    (q : X → Y) (F f : Y → ℂ) (h : X → ℂ)
    (hq : ContinuousOn q W) (hqS : MapsTo q W S)
    (hf : ContinuousOn f S) (hh : ContinuousOn h W)
    (hfe : EqOn (fun z => Complex.exp (f z)) F S)
    (hqh : EqOn (fun x => Complex.exp (h x)) (fun x => F (q x)) W)
    (hloop : q u = q v) : h u = h v := by
  have hfc : ContinuousOn (fun x => f (q x)) W := hf.comp hq hqS
  have he : EqOn (fun x => Complex.exp (f (q x)))
      (fun x => Complex.exp (h x)) W := by
    intro x hx
    exact (hfe (hqS hx)).trans (hqh hx).symm
  have hc := exp_lifts_diff_constant_on_preconnected W (fun x => f (q x)) h hW hfc hh he u hu v hv
  rw [hloop] at hc
  exact sub_right_inj.mp hc.symm


/-- The identity map on the complex unit circle has no continuous logarithm. -/
lemma no_log_unit_circle (f : ℂ → ℂ)
    (hf : ContinuousOn f (Metric.sphere 0 1))
    (heq : EqOn (fun z => Complex.exp (f z)) id (Metric.sphere 0 1)) : False := by
  let h : ℝ → ℂ := fun t => (t : ℂ) * Complex.I
  let q : ℝ → ℂ := fun t => Complex.exp (h t)
  have hh : Continuous h := Complex.continuous_ofReal.mul continuous_const
  have hq : Continuous q := Complex.continuous_exp.comp hh
  have hqS : MapsTo q univ (Metric.sphere 0 1) := by
    intro t ht
    simpa [q, h, Metric.mem_sphere, dist_zero_right] using Complex.norm_exp_ofReal_mul_I t
  have hloop : q 0 = q (2 * Real.pi) := by
    simp [q, h, Complex.exp_two_pi_mul_I]
  have he : EqOn (fun x => Complex.exp (h x)) (fun x => id (q x)) univ := by
    intro x hx
    rfl
  have hc : h 0 = h (2 * Real.pi) :=
    log_lift_increment_eq_zero_on_closed_loop univ isPreconnected_univ
      (Metric.sphere 0 1) 0 (2 * Real.pi) (mem_univ _) (mem_univ _)
      q id f h hq.continuousOn hqS hf hh.continuousOn heq he hloop
  have hn : ((2 * Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt Real.two_pi_pos)) Complex.I_ne_zero
  apply hn
  simpa [h] using hc.symm

open Set

/-- A logarithm of the ratio on a closed set produces a continuous map on the
plane whose unique zero is b and whose values on the set are z-a. -/
lemma continuous_unique_zero_extension_of_log_ratio
    (K : Set ℂ) (hK : IsClosed K) (a b : ℂ) (hb : b ∉ K)
    (f : ℂ → ℂ) (hf : ContinuousOn f K)
    (heq : EqOn (fun z => Complex.exp (f z)) (fun z => (z-a)/(z-b)) K) :
    ∃ H : ℂ → ℂ, Continuous H ∧ (∀ z, H z = 0 ↔ z = b) ∧
      EqOn H (fun z => z-a) K := by
  let fk : C(K, ℂ) := ⟨K.domRestrict f, hf.domRestrict⟩
  obtain ⟨fext, hfext⟩ := fk.exists_restrict_eq hK
  have hfe (z : ℂ) (hz : z ∈ K) : fext z = f z := by
    have h := congrArg (fun q : C(K, ℂ) => q ⟨z, hz⟩) hfext
    exact h
  let H : ℂ → ℂ := fun z => (z-b) * Complex.exp (fext z)
  refine ⟨H, (continuous_id.sub continuous_const).mul
    (Complex.continuous_exp.comp fext.continuous), ?_, ?_⟩
  · intro z
    simp [H, Complex.exp_ne_zero, sub_eq_zero]
  · intro z hz
    change (z-b) * Complex.exp (fext z) = z-a
    have hz0 : z-b ≠ 0 := by
      intro h
      have hzb : z = b := sub_eq_zero.mp h
      subst z
      exact hb hz
    have he : Complex.exp (f z) = (z-a)/(z-b) := heq hz
    rw [hfe z hz, he]
    field_simp


/-- Every component of an open set has boundary outside the open set. -/
lemma frontier_connectedComponentIn_subset_compl
    {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    (O : Set X) (hO : IsOpen O) (a : X) (ha : a ∈ O) :
    frontier (connectedComponentIn O a) ⊆ Oᶜ := by
  let C := connectedComponentIn O a
  have hC : C ⊆ O := connectedComponentIn_subset O a
  have haC : a ∈ C := mem_connectedComponentIn ha
  have hO' : IsOpen C := hO.connectedComponentIn
  have hpre : IsPreconnected C := isPreconnected_connectedComponentIn
  have hclpre : IsPreconnected (closure C ∩ O) :=
    hpre.subset_closure (fun x hx => ⟨subset_closure hx, hC hx⟩) inter_subset_left
  have hclsub : closure C ∩ O ⊆ C :=
    hclpre.subset_connectedComponentIn ⟨subset_closure haC, ha⟩ inter_subset_right
  intro x hx hxO
  have hxcl : x ∈ closure C := frontier_subset_closure hx
  have hxC : x ∈ C := hclsub ⟨hxcl, hxO⟩
  have hxint : x ∈ interior C := by rw [hO'.interior_eq]; exact hxC
  exact (disjoint_left.mp disjoint_interior_frontier) hxint hx

open Set

/-- A global zero-free map cannot agree with z-a outside a bounded set. -/
lemma no_global_zero_free_eq_sub_outside_bounded
    (C : Set ℂ) (hC : Bornology.IsBounded C) (a : ℂ) (H : ℂ → ℂ)
    (hH : Continuous H) (hHz : ∀ z, H z ≠ 0)
    (hEq : ∀ z ∉ C, H z = z-a) : False := by
  letI : ContractibleSpace (Set.univ : Set ℂ) :=
    (convex_univ : Convex ℝ (Set.univ : Set ℂ)).contractibleSpace univ_nonempty
  have hsc : IsSimplyConnected (Set.univ : Set ℂ) := SimplyConnectedSpace.ofContractible _
  have h0 : 0 ∉ H '' Set.univ := by
    rintro ⟨z, hz, he⟩
    exact hHz z he
  obtain ⟨F, hFc, hFe⟩ := Complex.exists_continuousOn_eqOn_exp_comp
    hsc isOpen_univ hH.continuousOn h0
  obtain ⟨r, hr, hCr⟩ := hC.subset_ball_lt 0 a
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  let ψ : ℂ → ℂ := fun z => a + (r : ℂ) * z
  have hψc : Continuous ψ := continuous_const.add (continuous_const.mul continuous_id)
  have hψout (z : ℂ) (hz : z ∈ Metric.sphere 0 1) : ψ z ∉ C := by
    have hz1 : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    have hdist : dist (ψ z) a = r := by
      simp [ψ, dist_eq_norm, norm_mul, Complex.norm_real, abs_of_pos hr, hz1]
    intro hzC
    have hzball := hCr hzC
    have : dist (ψ z) a < r := hzball
    rw [hdist] at this
    exact (lt_irrefl _) this
  let f : ℂ → ℂ := fun z => F (ψ z) - Complex.log (r : ℂ)
  have hfc : ContinuousOn f (Metric.sphere 0 1) := by
    have hF : Continuous F := continuousOn_univ.mp hFc
    exact ((hF.comp hψc).sub continuous_const).continuousOn
  apply no_log_unit_circle f hfc
  intro z hz
  change Complex.exp (F (ψ z) - Complex.log (r : ℂ)) = z
  have hexp : Complex.exp (F (ψ z)) = H (ψ z) := hFe (mem_univ _)
  rw [Complex.exp_sub, hexp, hEq _ (hψout z hz), Complex.exp_log hr0]
  dsimp [ψ]
  field_simp
  ring


/-- A continuous map agreeing with z-a on the boundary of a bounded open set
must have a zero inside whenever a is inside. -/
lemma zero_inside_of_boundary_eq_sub
    (C : Set ℂ) (hCo : IsOpen C) (hCb : Bornology.IsBounded C)
    (a : ℂ) (ha : a ∈ C) (H : ℂ → ℂ) (hH : ContinuousOn H (closure C))
    (hEq : EqOn H (fun z => z-a) (frontier C)) :
    ∃ z ∈ C, H z = 0 := by
  classical
  by_contra hn
  have hHnz : ∀ z ∈ C, H z ≠ 0 := by
    intro z hz hzero
    exact hn ⟨z, hz, hzero⟩
  let G := (closure C).piecewise H (fun z => z-a)
  have hGcl : EqOn G H (closure C) := by
    intro z hz
    simp [G, hz]
  have hGout : EqOn G (fun z => z-a) Cᶜ := by
    intro z hz
    by_cases hzcl : z ∈ closure C
    · have hzfr : z ∈ frontier C := by
        rw [hCo.frontier_eq]
        exact ⟨hzcl, hz⟩
      simpa [G, hzcl] using hEq hzfr
    · simp [G, hzcl]
  have hGc : Continuous G := by
    have hc1 : ContinuousOn G (closure C) := hH.congr hGcl
    have hc2 : ContinuousOn G Cᶜ :=
      (continuous_id.sub continuous_const).continuousOn.congr hGout
    have hcu : ContinuousOn G (closure C ∪ Cᶜ) :=
      hc1.union_of_isClosed hc2 isClosed_closure hCo.isClosed_compl
    have hu : closure C ∪ Cᶜ = univ := by
      apply eq_univ_iff_forall.mpr
      intro z
      by_cases hz : z ∈ C
      · exact Or.inl (subset_closure hz)
      · exact Or.inr hz
    rw [hu] at hcu
    exact continuousOn_univ.mp hcu
  have hGnz : ∀ z, G z ≠ 0 := by
    intro z
    by_cases hz : z ∈ C
    · rw [hGcl (subset_closure hz)]
      exact hHnz z hz
    · rw [hGout hz]
      exact sub_ne_zero.mpr (fun h => hz (h ▸ ha))
  exact no_global_zero_free_eq_sub_outside_bounded C hCb a G hGc hGnz hGout


/-- The logarithm-to-connectivity converse when the component of a is bounded. -/
lemma log_ratio_forces_b_in_bounded_component
    (K : Set ℂ) (hK : IsClosed K) (a b : ℂ) (ha : a ∉ K) (hb : b ∉ K)
    (hbounded : Bornology.IsBounded (connectedComponentIn Kᶜ a))
    (f : ℂ → ℂ) (hf : ContinuousOn f K)
    (heq : EqOn (fun z => Complex.exp (f z)) (fun z => (z-a)/(z-b)) K) :
    b ∈ connectedComponentIn Kᶜ a := by
  let C := connectedComponentIn Kᶜ a
  have hCo : IsOpen C := hK.isOpen_compl.connectedComponentIn
  have haC : a ∈ C := mem_connectedComponentIn ha
  have hfr : frontier C ⊆ K := by
    have h := frontier_connectedComponentIn_subset_compl Kᶜ hK.isOpen_compl a ha
    simpa using h
  obtain ⟨H, hH, hzero, hEq⟩ :=
    continuous_unique_zero_extension_of_log_ratio K hK a b hb f hf heq
  obtain ⟨z, hzC, hz⟩ := zero_inside_of_boundary_eq_sub C hCo hbounded a haC
    H hH.continuousOn (hEq.mono hfr)
  have hzb : z = b := (hzero z).mp hz
  simpa [hzb] using hzC

open Set

/-- If a bounded set has preconnected complement, two distinct components of
any subset of its complement cannot both be unbounded. -/
lemma two_unbounded_components_meet
    {X : Type} [PseudoMetricSpace X] (K B : Set X) (hKB : K ⊆ B)
    (hB : Bornology.IsBounded B) (hBc : IsPreconnected Bᶜ)
    (a b : X) (hb : b ∉ K)
    (haun : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a))
    (hbun : ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b)) :
    b ∈ connectedComponentIn Kᶜ a := by
  have hexist {C : Set X} (hn : ¬ Bornology.IsBounded C) : ∃ x ∈ C, x ∉ B := by
    by_contra h
    apply hn
    apply hB.subset
    intro x hx
    by_contra hxB
    exact h ⟨x, hx, hxB⟩
  obtain ⟨x, hx, hxB⟩ := hexist haun
  obtain ⟨y, hy, hyB⟩ := hexist hbun
  have hBsub : Bᶜ ⊆ Kᶜ := compl_subset_compl.mpr hKB
  have hxy : y ∈ connectedComponentIn Kᶜ x :=
    hBc.subset_connectedComponentIn hxB hBsub hyB
  have heqa : connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ x :=
    connectedComponentIn_eq hx
  have hya : y ∈ connectedComponentIn Kᶜ a := heqa.symm ▸ hxy
  have heq : connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b :=
    (connectedComponentIn_eq hya).trans (connectedComponentIn_eq hy).symm
  rw [heq]
  exact mem_connectedComponentIn hb


/-- Every compact subset of the complex plane sits in a compact set with
preconnected complement. -/
lemma compact_subset_compact_with_preconnected_complement
    (K : Set ℂ) (hK : IsCompact K) :
    ∃ B : Set ℂ, K ⊆ B ∧ IsCompact B ∧ IsPreconnected Bᶜ := by
  let e : Schoenflies.Plane ≃ₜ ℂ :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans Homeomorph.finTwoArrow).trans
      Complex.equivRealProdCLM.symm.toHomeomorph
  have hpre : IsCompact (e ⁻¹' K) := e.isCompact_preimage.mpr hK
  obtain ⟨r, hr, hsub⟩ := Schoenflies.Plane.IsCompact.exists_closedSquare hpre
  let S := Schoenflies.Plane.closedSquare 0 r
  let B := e '' S
  have hSc : IsCompact S := Metric.isCompact_of_isClosed_isBounded
    (Schoenflies.Plane.isClosed_closedSquare 0 r) (Graph.isBounded_closedSquare r)
  have hBc : IsCompact B := hSc.image e.continuous
  have hKB : K ⊆ B := by
    intro z hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    apply hsub
    simpa using hz
  have hcomp : IsPreconnected Bᶜ := by
    have hc := (Schoenflies.Plane.isConnected_beyondSquare r).isPreconnected.image
      e e.continuous.continuousOn
    rw [Schoenflies.Plane.beyondSquare_eq_compl, e.image_compl] at hc
    exact hc
  exact ⟨B, hKB, hBc, hcomp⟩

open Set

/-- A continuous logarithm of (z-a)/(z-b) on a compact set forces a and b
into the same component of its complement. -/
theorem continuous_log_ratio_implies_same_component
    (K : Set ℂ) (hK : IsCompact K) (a b : ℂ) (ha : a ∉ K) (hb : b ∉ K)
    (f : ℂ → ℂ) (hf : ContinuousOn f K)
    (heq : EqOn (fun z => Complex.exp (f z)) (fun z => (z-a)/(z-b)) K) :
    b ∈ connectedComponentIn Kᶜ a := by
  by_cases hA : Bornology.IsBounded (connectedComponentIn Kᶜ a)
  · exact log_ratio_forces_b_in_bounded_component K hK.isClosed a b ha hb hA f hf heq
  · by_cases hB : Bornology.IsBounded (connectedComponentIn Kᶜ b)
    · have hinv : EqOn (fun z => Complex.exp (-f z)) (fun z => (z-b)/(z-a)) K := by
        intro z hz
        have hza : z-a ≠ 0 := by
          intro h
          have : z = a := sub_eq_zero.mp h
          subst z
          exact ha hz
        have hzb : z-b ≠ 0 := by
          intro h
          have : z = b := sub_eq_zero.mp h
          subst z
          exact hb hz
        have heqz : Complex.exp (f z) = (z-a)/(z-b) := heq hz
        change Complex.exp (-f z) = (z-b)/(z-a)
        rw [Complex.exp_neg, heqz]
        field_simp
      have hba : a ∈ connectedComponentIn Kᶜ b :=
        log_ratio_forces_b_in_bounded_component K hK.isClosed b a hb ha hB
          (fun z => -f z) hf.neg hinv
      have he : connectedComponentIn Kᶜ b = connectedComponentIn Kᶜ a :=
        connectedComponentIn_eq hba
      rw [← he]
      exact mem_connectedComponentIn hb
    · obtain ⟨B, hKB, hBc, hBconn⟩ :=
        compact_subset_compact_with_preconnected_complement K hK
      exact two_unbounded_components_meet K B hKB hBc.isBounded hBconn a b hb hA hB

open Set

/-- Janiszewski's theorem for two compact planar sets with preconnected
intersection, including the empty-intersection case. -/
theorem compact_janiszewski
    (S T : Set ℂ) (a b : ℂ) (hS : IsCompact S) (hT : IsCompact T)
    (hST : IsPreconnected (S ∩ T)) (ha : a ∉ S ∪ T) (hb : b ∉ S ∪ T)
    (habS : b ∈ connectedComponentIn Sᶜ a)
    (habT : b ∈ connectedComponentIn Tᶜ a) :
    b ∈ connectedComponentIn (S ∪ T)ᶜ a := by
  obtain ⟨f, hfc, hfe⟩ := continuous_log_ratio_of_same_component S hS.isClosed a b habS
  obtain ⟨g, hgc, hge⟩ := continuous_log_ratio_of_same_component T hT.isClosed a b habT
  have heq : EqOn (fun x => Complex.exp (f x)) (fun x => Complex.exp (g x)) (S ∩ T) := by
    intro z hz
    exact (hfe hz.1).trans (hge hz.2).symm
  obtain ⟨k, hkc, hkS, hkT⟩ :=
    glue_exp_lifts_preconnected S T f g hS.isClosed hT.isClosed hST hfc hgc heq
  apply continuous_log_ratio_implies_same_component (S ∪ T) (hS.union hT) a b ha hb k hkc
  intro z hz
  rcases hz with hz | hz
  · exact (hkS hz).trans (hfe hz)
  · exact (hkT hz).trans (hge hz)

open Set

noncomputable def inducedComponentMap {X : Type} [TopologicalSpace X]
    {U W : Set X} (hWU : W ⊆ U) : ConnectedComponents W → ConnectedComponents U :=
  Quotient.lift (fun x : W ↦ ConnectedComponents.mk (Set.inclusion hWU x)) (by
    intro x y hxy
    change connectedComponent x = connectedComponent y at hxy
    apply ConnectedComponents.coe_eq_coe'.mpr
    exact (continuous_inclusion hWU).mapsTo_connectedComponent y
      (connectedComponent_eq_iff_mem.mp hxy))

@[simp] lemma inducedComponentMap_mk {X : Type} [TopologicalSpace X]
    {U W : Set X} (hWU : W ⊆ U) (x : W) :
    inducedComponentMap hWU (ConnectedComponents.mk x) =
      ConnectedComponents.mk (Set.inclusion hWU x) := rfl


lemma component_mk_eq_iff {X : Type} [TopologicalSpace X] {U : Set X} (x y : U) :
    ConnectedComponents.mk x = ConnectedComponents.mk y ↔
      x.1 ∈ connectedComponentIn U y.1 := by
  rw [ConnectedComponents.coe_eq_coe', connectedComponentIn_eq_image y.2]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨z, hz, hzx⟩
    have : z = x := Subtype.ext hzx
    simpa only [this] using hz




open Set

lemma compact_component_clopen_split {X : Type} [TopologicalSpace X] [T2Space X]
    (K : Set X) (u v : X) (hK : IsCompact K) (hu : u ∈ K) (hv : v ∈ K)
    (hneq : v ∉ connectedComponentIn K u) :
    ∃ K₀ K₁ : Set X, IsCompact K₀ ∧ IsCompact K₁ ∧ Disjoint K₀ K₁ ∧
      K₀ ∪ K₁ = K ∧ u ∈ K₀ ∧ v ∈ K₁ := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let U : K := ⟨u, hu⟩
  let V : K := ⟨v, hv⟩
  have hnot : V ∉ connectedComponent U := by
    intro h
    apply hneq
    rw [connectedComponentIn_eq_image hu]
    exact ⟨V, h, rfl⟩
  rw [connectedComponent_eq_iInter_isClopen] at hnot
  simp only [mem_iInter, not_forall] at hnot
  obtain ⟨s, hvs⟩ := hnot
  let K₀ : Set X := Subtype.val '' (s : Set K)
  let K₁ : Set X := Subtype.val '' (s : Set K)ᶜ
  have hcomp₀ : IsCompact K₀ := s.property.1.1.isCompact.image continuous_subtype_val
  have hcomp₁ : IsCompact K₁ := s.property.1.compl.1.isCompact.image continuous_subtype_val
  have hdisj : Disjoint K₀ K₁ := by
    apply Set.disjoint_left.mpr
    rintro z ⟨p, hp, rfl⟩ ⟨q, hq, hqp⟩
    have h : q = p := Subtype.ext hqp
    subst q
    exact hq hp
  refine ⟨K₀, K₁, hcomp₀, hcomp₁, hdisj, ?_, ?_, ?_⟩
  · ext z
    constructor
    · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩) <;> exact p.property
    · intro hz
      by_cases h : (⟨z, hz⟩ : K) ∈ (s : Set K)
      · exact Or.inl ⟨⟨z, hz⟩, h, rfl⟩
      · exact Or.inr ⟨⟨z, hz⟩, h, rfl⟩
  · exact ⟨U, s.property.2, rfl⟩
  · exact ⟨V, hvs, rfl⟩



/-- Conditional on Janiszewski's separation theorem, adding a nonseparating compact
arc between two disjoint compact pieces cannot split an existing complementary region. -/
lemma attachment_between_pieces_preserves_components
    {X : Type} [TopologicalSpace X]
    (jan : ∀ S T : Set X, IsCompact S → IsCompact T → (∃ p, S ∩ T = {p}) →
      ∀ x y : X, y ∈ connectedComponentIn Sᶜ x → y ∈ connectedComponentIn Tᶜ x →
      y ∈ connectedComponentIn (S ∪ T)ᶜ x)
    (K₀ K₁ A : Set X) (u v x y : X)
    (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁) (hA : IsCompact A)
    (h₀ : K₀ ∩ A = {u}) (h₁ : (K₀ ∪ A) ∩ K₁ = {v})
    (hAc : IsPreconnected Aᶜ)
    (hx : x ∈ (K₀ ∪ K₁ ∪ A)ᶜ)
    (hy : y ∈ (K₀ ∪ K₁ ∪ A)ᶜ)
    (hxy : y ∈ connectedComponentIn (K₀ ∪ K₁)ᶜ x) :
    y ∈ connectedComponentIn (K₀ ∪ K₁ ∪ A)ᶜ x := by
  have hxA : x ∈ Aᶜ := by simpa only [mem_compl_iff, mem_union] using fun h : x ∈ A => hx (Or.inr h)
  have hyA : y ∈ Aᶜ := by simpa only [mem_compl_iff, mem_union] using fun h : y ∈ A => hy (Or.inr h)
  have hxyA : y ∈ connectedComponentIn Aᶜ x :=
    hAc.subset_connectedComponentIn hxA subset_rfl hyA
  have hxyK₀ : y ∈ connectedComponentIn K₀ᶜ x :=
    connectedComponentIn_mono x (compl_subset_compl.mpr subset_union_left) hxy
  have hxyK₁ : y ∈ connectedComponentIn K₁ᶜ x :=
    connectedComponentIn_mono x (compl_subset_compl.mpr subset_union_right) hxy
  have hfirst : y ∈ connectedComponentIn (K₀ ∪ A)ᶜ x :=
    jan K₀ A hK₀ hA ⟨u, h₀⟩ x y hxyK₀ hxyA
  have hlast : y ∈ connectedComponentIn ((K₀ ∪ A) ∪ K₁)ᶜ x :=
    jan (K₀ ∪ A) K₁ (hK₀.union hA) hK₁ ⟨v, h₁⟩ x y hfirst hxyK₁
  simpa only [union_assoc, union_comm, union_left_comm] using hlast


lemma attachment_partition_intersections
    {X : Type} (K₀ K₁ A : Set X) (u v : X)
    (hdisj : Disjoint K₀ K₁) (hu : u ∈ K₀) (hv : v ∈ K₁)
    (hinter : (K₀ ∪ K₁) ∩ A = {u, v}) :
    K₀ ∩ A = {u} ∧ (K₀ ∪ A) ∩ K₁ = {v} := by
  have huA : u ∈ A := by
    have h : u ∈ (K₀ ∪ K₁) ∩ A := by rw [hinter]; simp
    exact h.2
  have hvA : v ∈ A := by
    have h : v ∈ (K₀ ∪ K₁) ∩ A := by rw [hinter]; simp
    exact h.2
  have hnot : ∀ z, ¬ (z ∈ K₀ ∧ z ∈ K₁) := by
    intro z hz
    exact Set.disjoint_left.mp hdisj hz.1 hz.2
  constructor
  · ext z
    simp only [mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hz₀, hzA⟩
      have hz : z ∈ ({u, v} : Set X) := by
        rw [← hinter]
        exact ⟨Or.inl hz₀, hzA⟩
      simp only [mem_insert_iff, mem_singleton_iff] at hz
      rcases hz with h | h
      · exact h
      · subst z
        exact (hnot v ⟨hz₀, hv⟩).elim
    · intro hz
      subst z
      exact ⟨hu, huA⟩
  · ext z
    simp only [mem_inter_iff, mem_union, mem_singleton_iff]
    constructor
    · rintro ⟨hz₀ | hzA, hz₁⟩
      · exact (hnot z ⟨hz₀, hz₁⟩).elim
      · have hz : z ∈ ({u, v} : Set X) := by
          rw [← hinter]
          exact ⟨Or.inr hz₁, hzA⟩
        simp only [mem_insert_iff, mem_singleton_iff] at hz
        rcases hz with h | h
        · subst z
          exact (hnot u ⟨hu, hz₁⟩).elim
        · exact h
    · intro hz
      subst z
      exact ⟨Or.inr hvA, hv⟩


lemma attachment_preserves_components_of_disjoint_compact_pieces
    {X : Type} [TopologicalSpace X]
    (jan : ∀ S T : Set X, IsCompact S → IsCompact T → (∃ p, S ∩ T = {p}) →
      ∀ x y : X, y ∈ connectedComponentIn Sᶜ x → y ∈ connectedComponentIn Tᶜ x →
      y ∈ connectedComponentIn (S ∪ T)ᶜ x)
    (K₀ K₁ A : Set X) (u v x y : X)
    (hK₀ : IsCompact K₀) (hK₁ : IsCompact K₁) (hA : IsCompact A)
    (hdisj : Disjoint K₀ K₁) (hu : u ∈ K₀) (hv : v ∈ K₁)
    (hinter : (K₀ ∪ K₁) ∩ A = {u, v}) (hAc : IsPreconnected Aᶜ)
    (hx : x ∈ (K₀ ∪ K₁ ∪ A)ᶜ) (hy : y ∈ (K₀ ∪ K₁ ∪ A)ᶜ)
    (hxy : y ∈ connectedComponentIn (K₀ ∪ K₁)ᶜ x) :
    y ∈ connectedComponentIn (K₀ ∪ K₁ ∪ A)ᶜ x := by
  obtain ⟨h₀, h₁⟩ := attachment_partition_intersections K₀ K₁ A u v hdisj hu hv hinter
  exact attachment_between_pieces_preserves_components jan K₀ K₁ A u v x y
    hK₀ hK₁ hA h₀ h₁ hAc hx hy hxy


lemma attachment_different_components_preserves
    {X : Type} [TopologicalSpace X] [T2Space X]
    (jan : ∀ S T : Set X, IsCompact S → IsCompact T → (∃ p, S ∩ T = {p}) →
      ∀ x y : X, y ∈ connectedComponentIn Sᶜ x → y ∈ connectedComponentIn Tᶜ x →
      y ∈ connectedComponentIn (S ∪ T)ᶜ x)
    (K A : Set X) (u v x y : X)
    (hK : IsCompact K) (hA : IsCompact A) (hu : u ∈ K) (hv : v ∈ K)
    (hneq : v ∉ connectedComponentIn K u)
    (hinter : K ∩ A = {u, v}) (hAc : IsPreconnected Aᶜ)
    (hx : x ∈ (K ∪ A)ᶜ) (hy : y ∈ (K ∪ A)ᶜ)
    (hxy : y ∈ connectedComponentIn Kᶜ x) :
    y ∈ connectedComponentIn (K ∪ A)ᶜ x := by
  obtain ⟨K₀, K₁, hk₀, hk₁, hdisj, hunion, hu₀, hv₁⟩ :=
    compact_component_clopen_split K u v hK hu hv hneq
  have hinter' : (K₀ ∪ K₁) ∩ A = {u, v} := by rw [hunion]; exact hinter
  have hx' : x ∈ (K₀ ∪ K₁ ∪ A)ᶜ := by simpa only [hunion] using hx
  have hy' : y ∈ (K₀ ∪ K₁ ∪ A)ᶜ := by simpa only [hunion] using hy
  have hxy' : y ∈ connectedComponentIn (K₀ ∪ K₁)ᶜ x := by simpa only [hunion] using hxy
  have result := attachment_preserves_components_of_disjoint_compact_pieces jan K₀ K₁ A u v x y
    hk₀ hk₁ hA hdisj hu₀ hv₁ hinter' hAc hx' hy' hxy'
  simpa only [hunion] using result


noncomputable def componentEquivOfPreservation
    {X : Type} [TopologicalSpace X] {U W : Set X} (hWU : W ⊆ U)
    (hpreserve : ∀ x y : W, x.1 ∈ connectedComponentIn U y.1 →
      x.1 ∈ connectedComponentIn W y.1)
    (hmeet : ∀ x : U, ∃ y : W, y.1 ∈ connectedComponentIn U x.1) :
    ConnectedComponents W ≃ ConnectedComponents U := by
  apply Equiv.ofBijective (inducedComponentMap hWU)
  constructor
  · intro c d h
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe d
    rw [inducedComponentMap_mk, inducedComponentMap_mk] at h
    apply (component_mk_eq_iff x y).mpr
    apply hpreserve
    exact (component_mk_eq_iff (Set.inclusion hWU x) (Set.inclusion hWU y)).mp h
  · intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨y, hy⟩ := hmeet x
    refine ⟨ConnectedComponents.mk y, ?_⟩
    rw [inducedComponentMap_mk]
    exact (component_mk_eq_iff (Set.inclusion hWU y) x).mpr hy

lemma dense_complement_meets_component
    {X : Type} [TopologicalSpace X] [LocallyConnectedSpace X]
    (K A : Set X) (hK : IsClosed K) (hA : Dense Aᶜ) :
    ∀ x : (Kᶜ : Set X), ∃ y : ((K ∪ A)ᶜ : Set X), y.1 ∈ connectedComponentIn Kᶜ x.1 := by
  intro x
  have hopen : IsOpen (connectedComponentIn Kᶜ x.1) :=
    hK.isOpen_compl.connectedComponentIn
  obtain ⟨z, hzA, hzC⟩ := hA.exists_mem_open hopen
    ⟨x.1, mem_connectedComponentIn x.2⟩
  have hzK : z ∈ Kᶜ := connectedComponentIn_subset Kᶜ x.1 hzC
  have hz : z ∈ (K ∪ A)ᶜ := by simpa only [compl_union, mem_inter_iff] using And.intro hzK hzA
  exact ⟨⟨z, hz⟩, hzC⟩


noncomputable def attachmentDifferentComponentEquiv
    {X : Type} [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]
    (jan : ∀ S T : Set X, IsCompact S → IsCompact T → (∃ p, S ∩ T = {p}) →
      ∀ x y : X, y ∈ connectedComponentIn Sᶜ x → y ∈ connectedComponentIn Tᶜ x →
      y ∈ connectedComponentIn (S ∪ T)ᶜ x)
    (K A : Set X) (u v : X)
    (hK : IsCompact K) (hA : IsCompact A) (hu : u ∈ K) (hv : v ∈ K)
    (hneq : v ∉ connectedComponentIn K u) (hinter : K ∩ A = {u, v})
    (hAc : IsPreconnected Aᶜ) (hdense : Dense Aᶜ) :
    ConnectedComponents ((K ∪ A)ᶜ : Set X) ≃ ConnectedComponents (Kᶜ : Set X) := by
  have hWU : (K ∪ A)ᶜ ⊆ Kᶜ := by
    intro z hz hzK
    exact hz (Or.inl hzK)
  apply componentEquivOfPreservation hWU
  · intro x y hxy
    exact attachment_different_components_preserves jan K A u v y.1 x.1
      hK hA hu hv hneq hinter hAc y.2 x.2 hxy
  · exact dense_complement_meets_component K A hK.isClosed hdense


lemma attachment_different_count
    {X : Type} [TopologicalSpace X] [T2Space X] [LocallyConnectedSpace X]
    (jan : ∀ S T : Set X, IsCompact S → IsCompact T → (∃ p, S ∩ T = {p}) →
      ∀ x y : X, y ∈ connectedComponentIn Sᶜ x → y ∈ connectedComponentIn Tᶜ x →
      y ∈ connectedComponentIn (S ∪ T)ᶜ x)
    (K A : Set X) (u v : X)
    (hK : IsCompact K) (hA : IsCompact A) (hu : u ∈ K) (hv : v ∈ K)
    (hneq : v ∉ connectedComponentIn K u) (hinter : K ∩ A = {u, v})
    (hAc : IsPreconnected Aᶜ) (hdense : Dense Aᶜ)
    (hfinite : Finite (ConnectedComponents (Kᶜ : Set X))) :
    Finite (ConnectedComponents ((K ∪ A)ᶜ : Set X)) ∧
      Nat.card (ConnectedComponents ((K ∪ A)ᶜ : Set X)) =
        Nat.card (ConnectedComponents (Kᶜ : Set X)) := by
  let e := attachmentDifferentComponentEquiv jan K A u v hK hA hu hv hneq hinter hAc hdense
  exact ⟨Finite.of_equiv _ e.symm, Nat.card_congr e⟩


open Set

/-- A nontrivial preconnected space that remains preconnected after deleting any point
has no continuous injective map into the real line. -/
lemma no_continuous_injective_to_real_of_punctured_preconnected
    {X : Type} [TopologicalSpace X] [PreconnectedSpace X] [Nontrivial X]
    (hpunct : ∀ z : X, IsPreconnected ({z}ᶜ : Set X))
    (f : X → ℝ) (hf : Continuous f) : ¬ Function.Injective f := by
  intro hinj
  obtain ⟨p, q, hpq⟩ := exists_pair_ne X
  have hfpq : f p ≠ f q := fun h => hpq (hinj h)
  have hxy : ∃ x y, f x < f y := by
    rcases lt_or_gt_of_ne hfpq with h | h
    · exact ⟨p, q, h⟩
    · exact ⟨q, p, h⟩
  obtain ⟨x, y, hlt⟩ := hxy
  let m : ℝ := (f x + f y) / 2
  have hxm : f x < m := left_lt_add_div_two.mpr hlt
  have hmy : m < f y := add_div_two_lt_right.mpr hlt
  have hrange : IsPreconnected (range f) := by
    simpa only [image_univ] using isPreconnected_univ.image f hf.continuousOn
  have hm : m ∈ range f := hrange.Icc_subset ⟨x, rfl⟩ ⟨y, rfl⟩ ⟨hxm.le, hmy.le⟩
  obtain ⟨z, hz⟩ := hm
  have hxz : x ≠ z := by intro h; subst x; exact (lt_irrefl _ (hz ▸ hxm))
  have hyz : y ≠ z := by intro h; subst y; exact (lt_irrefl _ (hz ▸ hmy))
  have hp : IsPreconnected (f '' ({z}ᶜ : Set X)) :=
    (hpunct z).image f hf.continuousOn
  have hfz : f z ∈ f '' ({z}ᶜ : Set X) :=
    hp.Icc_subset ⟨x, by simpa using hxz, rfl⟩ ⟨y, by simpa using hyz, rfl⟩
      ⟨by simpa [hz] using hxm.le, by simpa [hz] using hmy.le⟩
  obtain ⟨w, hw, hwz⟩ := hfz
  exact hw (hinj hwz)


/-- An embedded subset of the real line cannot contain the image of a space with no
continuous injection into the real line. -/
lemma no_embedding_range_contains_punctured_connected_space
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [PreconnectedSpace Y] [Nontrivial Y]
    (hpunct : ∀ z : Y, IsPreconnected ({z}ᶜ : Set Y))
    (P : Set ℝ) (f : P → X) (hf : Topology.IsEmbedding f)
    (g : Y → X) (hg : Continuous g) (hginj : Function.Injective g)
    (hsub : range g ⊆ range f) : False := by
  let g' : Y → range f := fun y => ⟨g y, hsub ⟨y, rfl⟩⟩
  have hg' : Continuous g' := hg.subtype_mk _
  have hginj' : Function.Injective g' := by
    intro x y h
    exact hginj (congrArg Subtype.val h)
  let k : Y → ℝ := fun y => (hf.toHomeomorph.symm (g' y)).1
  have hk : Continuous k := continuous_subtype_val.comp (hf.toHomeomorph.symm.continuous.comp hg')
  have hkinj : Function.Injective k := by
    intro x y h
    apply hginj'
    apply hf.toHomeomorph.symm.injective
    exact Subtype.ext h
  exact no_continuous_injective_to_real_of_punctured_preconnected hpunct k hk hkinj


/-- The image of an embedded real subset has dense complement in every real
normed space of dimension greater than one. -/
lemma dense_compl_range_real_embedding
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hrank : 1 < Module.rank ℝ E)
    (P : Set ℝ) (f : P → E) (hf : Topology.IsEmbedding f) : Dense (range f)ᶜ := by
  let : Nontrivial E := (rank_pos_iff_nontrivial (R := ℝ)).1 (zero_lt_one.trans hrank)
  apply interior_eq_empty_iff_dense_compl.mp
  apply Set.not_nonempty_iff_eq_empty.mp
  rintro ⟨c, hc⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior c hc
  let g := OpenPartialHomeomorph.univBall c r
  have hg : Continuous g := OpenPartialHomeomorph.continuous_univBall c r
  have hginj : Function.Injective g := by
    intro x y h
    apply g.injOn _ _ h <;> simp [g]
  have hsub : range g ⊆ range f := by
    rintro z ⟨x, rfl⟩
    apply interior_subset (hball ?_)
    have ht : g x ∈ g.target := g.map_source (by simp [g])
    simpa only [g, OpenPartialHomeomorph.univBall_target c hr] using ht
  have hpunct : ∀ z : E, IsPreconnected ({z}ᶜ : Set E) := fun z =>
    (isPathConnected_compl_singleton_of_one_lt_rank hrank z).isConnected.isPreconnected
  exact no_embedding_range_contains_punctured_connected_space hpunct P f hf g hg hginj hsub


lemma dense_compl_compact_injOn_real_image
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hrank : 1 < Module.rank ℝ E) (P : Set ℝ) (a : ℝ → E)
    (hP : IsCompact P) (ha : ContinuousOn a P) (hinj : Set.InjOn a P) :
    Dense (a '' P)ᶜ := by
  let : CompactSpace P := isCompact_iff_compactSpace.mp hP
  let f := P.domRestrict a
  have hfcont : Continuous f := ha.domRestrict
  have hfinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact hinj x.property y.property h
  have hf : Topology.IsEmbedding f := (hfcont.isClosedEmbedding hfinj).isEmbedding
  have h := dense_compl_range_real_embedding hrank P f hf
  simpa only [f, Set.range_domRestrict] using h

lemma planar_simple_arc_complement_dense (a : ℝ → ℝ × ℝ)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hinj : InjOn a (Icc (0 : ℝ) 1)) :
    Dense (a '' Icc (0 : ℝ) 1)ᶜ := by
  have hrank : 1 < Module.rank ℝ (ℝ × ℝ) := by
    simpa only [rank_prod', Module.rank_self, one_add_one_eq_two] using Cardinal.one_lt_two
  exact dense_compl_compact_injOn_real_image hrank _ a isCompact_Icc ha hinj

lemma arc_meets_compact_only_at_endpoints {X : Type} (K : Set X) (a : ℝ → X)
    (hzero : a 0 ∈ K) (hone : a 1 ∈ K)
    (hinterior : ∀ t ∈ Set.Ioo (0 : ℝ) 1, a t ∉ K) :
    K ∩ a '' Set.Icc (0 : ℝ) 1 = {a 0, a 1} := by
  ext z
  constructor
  · rintro ⟨hzK, t, ht, rfl⟩
    rcases lt_or_eq_of_le ht.1 with hpos | hzero'
    · rcases lt_or_eq_of_le ht.2 with hlt | hone'
      · exact (hinterior t ⟨hpos, hlt⟩ hzK).elim
      · subst t
        simp
    · subst t
      simp
  · intro hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨hzero, ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩⟩
    · exact ⟨hone, ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩⟩



lemma planar_arc_different_component_count
    (jan : ∀ S T : Set (ℝ × ℝ), IsCompact S → IsCompact T → (∃ p, S ∩ T = {p}) →
      ∀ x y, y ∈ connectedComponentIn Sᶜ x → y ∈ connectedComponentIn Tᶜ x →
      y ∈ connectedComponentIn (S ∪ T)ᶜ x)
    (K : Set (ℝ × ℝ)) (a : ℝ → ℝ × ℝ)
    (hK : IsCompact K) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hinj : InjOn a (Icc (0 : ℝ) 1)) (hu : a 0 ∈ K) (hv : a 1 ∈ K)
    (hinterior : ∀ t ∈ Ioo (0 : ℝ) 1, a t ∉ K)
    (hneq : a 1 ∉ connectedComponentIn K (a 0))
    (hnonsep : IsPreconnected (a '' Icc (0 : ℝ) 1)ᶜ)
    (hfinite : Finite (ConnectedComponents (Kᶜ : Set (ℝ × ℝ)))) :
    Finite (ConnectedComponents ((K ∪ a '' Icc (0 : ℝ) 1)ᶜ : Set (ℝ × ℝ))) ∧
      Nat.card (ConnectedComponents ((K ∪ a '' Icc (0 : ℝ) 1)ᶜ : Set (ℝ × ℝ))) =
        Nat.card (ConnectedComponents (Kᶜ : Set (ℝ × ℝ))) := by
  exact attachment_different_count jan K (a '' Icc (0 : ℝ) 1) (a 0) (a 1)
    hK (isCompact_Icc.image_of_continuousOn ha) hu hv hneq
    (arc_meets_compact_only_at_endpoints K a hu hv hinterior)
    hnonsep (planar_simple_arc_complement_dense a ha hinj) hfinite


open Set unitInterval

theorem subtypeArcIsSchoenfliesArc
    (α : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2))
    (hα : Continuous α) (hinj : Function.Injective α) :
    Schoenflies.IsArc (Set.range α) := by
  let f : ℝ → Schoenflies.Plane := fun t =>
    if ht : t ∈ I then α ⟨t, ht⟩ else 0
  have hf_eq (t : ℝ) (ht : t ∈ I) : f t = α ⟨t, ht⟩ := by
    simp only [f, dif_pos ht]
  have hf : ContinuousOn f I := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (I : Set ℝ).domRestrict f = α := by
      funext t
      exact hf_eq t.1 t.2
    simpa only [heq] using hα
  have hfi : InjOn f I := by
    intro x hx y hy hxy
    have hxy' : α ⟨x, hx⟩ = α ⟨y, hy⟩ := by
      simpa only [hf_eq x hx, hf_eq y hy] using hxy
    exact congrArg Subtype.val (hinj hxy')
  have hfr : f '' I = Set.range α := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, (hf_eq t ht).symm⟩
    · rintro ⟨⟨t, ht⟩, rfl⟩
      exact ⟨t, ht, hf_eq t ht⟩
  exact ⟨f, hf, hfi, hfr⟩



theorem auditedSimpleArcNonseparation
    (α : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2))
    (hα : Continuous α) (hinj : Function.Injective α) :
    IsConnected ((Set.range α)ᶜ) := by
  exact Schoenflies.isConnected_compl_arc
    (subtypeArcIsSchoenfliesArc α hα hinj)
    Schoenflies.squaresTwoConnected

/-- Transfer arc nonseparation from EuclideanSpace to the product plane. -/
theorem productPlaneArcNonseparation
    (a : ℝ → ℝ × ℝ) (ha : ContinuousOn a (Set.Icc (0 : ℝ) 1))
    (hinj : Set.InjOn a (Set.Icc (0 : ℝ) 1)) :
    IsPreconnected (a '' Set.Icc (0 : ℝ) 1)ᶜ := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans Homeomorph.finTwoArrow
  let α : Set.Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 2) := fun t => e.symm (a t.1)
  have hα : Continuous α := e.symm.continuous.comp ha.domRestrict
  have hαinj : Function.Injective α := by
    intro x y h
    apply Subtype.ext
    exact hinj x.property y.property (e.symm.injective h)
  have hcomp : IsPreconnected (Set.range α)ᶜ :=
    (auditedSimpleArcNonseparation α hα hαinj).isPreconnected
  have heq : e '' Set.range α = a '' Set.Icc (0 : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      exact ⟨t.1, t.2, by simp [α]⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨α ⟨t, ht⟩, ⟨⟨t, ht⟩, rfl⟩, by simp [α]⟩
  have h := hcomp.image e e.continuous.continuousOn
  rwa [e.image_compl, heq] at h


theorem planar_arc_different_count_of_singleton_janiszewski
    (jan : ∀ S T : Set (ℝ × ℝ), IsCompact S → IsCompact T → (∃ p, S ∩ T = {p}) →
      ∀ x y, y ∈ connectedComponentIn Sᶜ x → y ∈ connectedComponentIn Tᶜ x →
      y ∈ connectedComponentIn (S ∪ T)ᶜ x)
    (K : Set (ℝ × ℝ)) (a : ℝ → ℝ × ℝ)
    (hK : IsCompact K) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hinj : InjOn a (Icc (0 : ℝ) 1)) (hu : a 0 ∈ K) (hv : a 1 ∈ K)
    (hinterior : ∀ t ∈ Ioo (0 : ℝ) 1, a t ∉ K)
    (hneq : a 1 ∉ connectedComponentIn K (a 0))
    (hfinite : Finite (ConnectedComponents (Kᶜ : Set (ℝ × ℝ)))) :
    Finite (ConnectedComponents ((K ∪ a '' Icc (0 : ℝ) 1)ᶜ : Set (ℝ × ℝ))) ∧
      Nat.card (ConnectedComponents ((K ∪ a '' Icc (0 : ℝ) 1)ᶜ : Set (ℝ × ℝ))) =
        Nat.card (ConnectedComponents (Kᶜ : Set (ℝ × ℝ))) := by
  exact planar_arc_different_component_count jan K a hK ha hinj hu hv hinterior hneq
    (productPlaneArcNonseparation a ha hinj) hfinite

open Set

/-- The singleton-intersection form of Janiszewski transfers from ℂ to ℝ×ℝ. -/
lemma product_singleton_janiszewski
    (S T : Set (ℝ × ℝ)) (hS : IsCompact S) (hT : IsCompact T)
    (hint : ∃ p, S ∩ T = {p}) (x y : ℝ × ℝ)
    (hSxy : y ∈ connectedComponentIn Sᶜ x)
    (hTxy : y ∈ connectedComponentIn Tᶜ x) :
    y ∈ connectedComponentIn (S ∪ T)ᶜ x := by
  let e : (ℝ × ℝ) ≃ₜ ℂ := Complex.equivRealProdCLM.symm.toHomeomorph
  have hxS : x ∈ Sᶜ := connectedComponentIn_nonempty_iff.mp ⟨y, hSxy⟩
  have hxT : x ∈ Tᶜ := connectedComponentIn_nonempty_iff.mp ⟨y, hTxy⟩
  have hyS : y ∈ Sᶜ := connectedComponentIn_subset _ _ hSxy
  have hyT : y ∈ Tᶜ := connectedComponentIn_subset _ _ hTxy
  have hSxy' : e y ∈ connectedComponentIn (e '' S)ᶜ (e x) := by
    have h := e.continuous.continuousOn.mapsTo_connectedComponentIn hxS hSxy
    rwa [e.image_compl] at h
  have hTxy' : e y ∈ connectedComponentIn (e '' T)ᶜ (e x) := by
    have h := e.continuous.continuousOn.mapsTo_connectedComponentIn hxT hTxy
    rwa [e.image_compl] at h
  have hInter : IsPreconnected ((e '' S) ∩ (e '' T)) := by
    obtain ⟨p, hp⟩ := hint
    rw [← Set.image_inter e.injective, hp, image_singleton]
    exact isPreconnected_singleton
  have hxU : e x ∉ (e '' S) ∪ (e '' T) := by
    change e x ∈ ((e '' S) ∪ (e '' T))ᶜ
    rw [← image_union, ← e.image_compl]
    exact mem_image_of_mem e (by simpa only [compl_union, mem_inter_iff] using And.intro hxS hxT)
  have hyU : e y ∉ (e '' S) ∪ (e '' T) := by
    change e y ∈ ((e '' S) ∪ (e '' T))ᶜ
    rw [← image_union, ← e.image_compl]
    exact mem_image_of_mem e (by simpa only [compl_union, mem_inter_iff] using And.intro hyS hyT)
  have h := compact_janiszewski (e '' S) (e '' T) (e x) (e y)
    (hS.image e.continuous) (hT.image e.continuous) hInter hxU hyU hSxy' hTxy'
  have hxU' : e x ∈ ((e '' S) ∪ (e '' T))ᶜ := hxU
  have hh := e.symm.continuous.continuousOn.mapsTo_connectedComponentIn hxU' h
  have himage : e.symm '' (((e '' S) ∪ (e '' T))ᶜ) = (S ∪ T)ᶜ := by
    rw [← image_union, ← e.image_compl]
    exact e.toEquiv.symm_image_image ((S ∪ T)ᶜ)
  rw [himage] at hh
  simpa using hh


/-- The different-component branch of the arc-attachment count theorem. -/
theorem solution
    (K : Set (ℝ × ℝ)) (a : ℝ → ℝ × ℝ)
    (hK : IsCompact K) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hinj : InjOn a (Icc (0 : ℝ) 1)) (hu : a 0 ∈ K) (hv : a 1 ∈ K)
    (hinterior : ∀ t ∈ Ioo (0 : ℝ) 1, a t ∉ K)
    (hneq : a 1 ∉ connectedComponentIn K (a 0))
    (hfinite : Finite (ConnectedComponents (Kᶜ : Set (ℝ × ℝ)))) :
    Finite (ConnectedComponents ((K ∪ a '' Icc (0 : ℝ) 1)ᶜ : Set (ℝ × ℝ))) ∧
      Nat.card (ConnectedComponents ((K ∪ a '' Icc (0 : ℝ) 1)ᶜ : Set (ℝ × ℝ))) =
        Nat.card (ConnectedComponents (Kᶜ : Set (ℝ × ℝ))) := by
  exact planar_arc_different_count_of_singleton_janiszewski
    product_singleton_janiszewski K a hK ha hinj hu hv hinterior hneq hfinite

#print axioms solution
