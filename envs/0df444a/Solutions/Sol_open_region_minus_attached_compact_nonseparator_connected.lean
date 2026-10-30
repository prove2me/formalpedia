-- Prove2me | solution 1 for open_region_minus_attached_compact_nonseparator_connected
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T02:55:37.223256+00:00
-- url     : https://prove2.me/submissions/fc658fab-aa77-4059-8d1c-a26d4d7bd2a7

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

open Set Metric

/-- If a preconnected set meets a ball but misses its sphere, it lies in the ball. -/
lemma preconnected_inside_ball {X : Type} [PseudoMetricSpace X]
    (C : Set X) (hC : IsPreconnected C) (c x : X) (r : ℝ)
    (hxC : x ∈ C) (hxball : x ∈ ball c r) (hsphere : Disjoint C (sphere c r)) :
    C ⊆ ball c r := by
  intro z hz
  have hdist : ContinuousOn (fun w : X => dist w c) C :=
    (continuous_id.dist continuous_const).continuousOn
  have hne : ∀ w ∈ C, dist w c ≠ r := by
    intro w hw heq
    exact (disjoint_left.mp hsphere) hw heq
  exact hC.gt_of_ne hdist hne ⟨x, hxC, hxball⟩ hz

/-- Janiszewski's theorem when one set is compact and the other closed. -/
theorem compact_closed_janiszewski
    (S T : Set ℂ) (a b : ℂ) (hS : IsCompact S) (hT : IsClosed T)
    (hST : IsPreconnected (S ∩ T))
    (habS : b ∈ connectedComponentIn Sᶜ a)
    (habT : b ∈ connectedComponentIn Tᶜ a) :
    b ∈ connectedComponentIn (S ∪ T)ᶜ a := by
  have haT : a ∈ Tᶜ := connectedComponentIn_nonempty_iff.mp ⟨b, habT⟩
  let D := connectedComponentIn Tᶜ a
  have hDo : IsOpen D := hT.isOpen_compl.connectedComponentIn
  have hDc : IsConnected D := isConnected_connectedComponentIn_iff.mpr haT
  have hDp : IsPathConnected D := hDo.isConnected_iff_isPathConnected.mp hDc
  obtain ⟨γ, hγ⟩ := hDp.joinedIn a (mem_connectedComponentIn haT) b habT
  let C : Set ℂ := Set.range γ
  have hCcompact : IsCompact C := isCompact_range γ.continuous
  have hCpre : IsPreconnected C := isPreconnected_range γ.continuous
  have haC : a ∈ C := ⟨0, γ.source⟩
  have hbC : b ∈ C := ⟨1, γ.target⟩
  have hCT : C ⊆ Tᶜ := by
    rintro z ⟨t, rfl⟩
    exact connectedComponentIn_subset Tᶜ a (hγ t)
  obtain ⟨r, hr, hrbound⟩ := (hCcompact.union hS).isBounded.subset_ball_lt 0 0
  have hCr : C ⊆ ball (0 : ℂ) r := fun z hz => hrbound (Or.inl hz)
  have hSr : S ⊆ ball (0 : ℂ) r := fun z hz => hrbound (Or.inr hz)
  let F : Set ℂ := (T ∩ closedBall 0 r) ∪ sphere 0 r
  have hBall : IsCompact (closedBall (0 : ℂ) r) := isCompact_closedBall 0 r
  have hSphere : IsCompact (sphere (0 : ℂ) r) := isCompact_sphere 0 r
  have hFcompact : IsCompact F := (hBall.inter_left hT).union hSphere
  have hSF : S ∩ F = S ∩ T := by
    ext z
    constructor
    · rintro ⟨hzS, hzT | hzSphere⟩
      · exact ⟨hzS, hzT.1⟩
      · have hzBall := hSr hzS
        have hlt : dist z (0 : ℂ) < r := hzBall
        have heq : dist z (0 : ℂ) = r := hzSphere
        exact False.elim ((ne_of_lt hlt) heq)
    · rintro ⟨hzS, hzT⟩
      refine ⟨hzS, Or.inl ⟨hzT, ?_⟩⟩
      exact ball_subset_closedBall (hSr hzS)
  have hCF : C ⊆ Fᶜ := by
    intro z hz hzF
    rcases hzF with hzT | hzSphere
    · exact hCT hz hzT.1
    · have hlt : dist z (0 : ℂ) < r := hCr hz
      have heq : dist z (0 : ℂ) = r := hzSphere
      exact (ne_of_lt hlt) heq
  have habF : b ∈ connectedComponentIn Fᶜ a :=
    hCpre.subset_connectedComponentIn haC hCF hbC
  have haS : a ∈ Sᶜ := connectedComponentIn_nonempty_iff.mp ⟨b, habS⟩
  have hbS : b ∈ Sᶜ := connectedComponentIn_subset _ _ habS
  have haF : a ∈ Fᶜ := hCF haC
  have hbF : b ∈ Fᶜ := hCF hbC
  have habSF : b ∈ connectedComponentIn (S ∪ F)ᶜ a :=
    compact_janiszewski S F a b hS hFcompact (hSF ▸ hST)
      (fun h => h.elim haS haF) (fun h => h.elim hbS hbF) habS habF
  let R := connectedComponentIn (S ∪ F)ᶜ a
  have haR : a ∈ R := mem_connectedComponentIn (fun h => h.elim haS haF)
  have hRpre : IsPreconnected R := isPreconnected_connectedComponentIn
  have hRsphere : Disjoint R (sphere (0 : ℂ) r) := by
    apply disjoint_left.mpr
    intro z hzR hzSphere
    have hz : z ∈ (S ∪ F)ᶜ := connectedComponentIn_subset _ _ hzR
    exact hz (Or.inr (Or.inr hzSphere))
  have hRball : R ⊆ ball (0 : ℂ) r :=
    preconnected_inside_ball R hRpre 0 a r haR (hCr haC) hRsphere
  have hRsub : R ⊆ (S ∪ T)ᶜ := by
    intro z hzR hzUnion
    have hzSF : z ∈ (S ∪ F)ᶜ := connectedComponentIn_subset _ _ hzR
    rcases hzUnion with hzS | hzT
    · exact hzSF (Or.inl hzS)
    · exact hzSF (Or.inr (Or.inl ⟨hzT, ball_subset_closedBall (hRball hzR)⟩))
  exact hRpre.subset_connectedComponentIn haR hRsub habSF



open Set

/-- General open-region nonseparation, conditional here on the compact/closed
Janiszewski theorem imported from the working draft. -/
lemma open_region_minus_attached_nonseparator_preconnected
    (U A : Set ℂ) (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hAc : IsCompact A) (hAcompl : IsPreconnected Aᶜ)
    (hinter : IsPreconnected (A ∩ Uᶜ)) :
    IsPreconnected (U \ A) := by
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  have hxyU : y ∈ connectedComponentIn U x :=
    hUc.subset_connectedComponentIn hx.1 Subset.rfl hy.1
  have hxyA : y ∈ connectedComponentIn Aᶜ x :=
    hAcompl.subset_connectedComponentIn hx.2 Subset.rfl hy.2
  have hxy : y ∈ connectedComponentIn (A ∪ Uᶜ)ᶜ x :=
    compact_closed_janiszewski A Uᶜ x y hAc hUo.isClosed_compl hinter hxyA
      (by simpa using hxyU)
  have hset : (A ∪ Uᶜ)ᶜ = U \ A := by
    ext z
    simp [and_comm]
  rw [hset] at hxy
  exact ⟨connectedComponentIn (U \ A) x, connectedComponentIn_subset _ _,
    mem_connectedComponentIn hx, hxy, isPreconnected_connectedComponentIn⟩


/-- If the added nonseparator has dense complement, every nonempty open
connected region remains connected after removal. -/
theorem solution
    (U A : Set ℂ) (hUo : IsOpen U) (hUc : IsConnected U)
    (hAc : IsCompact A) (hAcompl : IsPreconnected Aᶜ) (hAdense : Dense Aᶜ)
    (hinter : IsPreconnected (A ∩ Uᶜ)) :
    IsConnected (U \ A) := by
  obtain ⟨z, hzA, hzU⟩ := hAdense.exists_mem_open hUo hUc.nonempty
  exact ⟨⟨z, hzU, hzA⟩,
    open_region_minus_attached_nonseparator_preconnected U A hUo hUc.isPreconnected
      hAc hAcompl hinter⟩


#print axioms solution
