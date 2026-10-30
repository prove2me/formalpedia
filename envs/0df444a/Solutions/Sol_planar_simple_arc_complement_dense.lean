-- Prove2me | solution 1 for planar_simple_arc_complement_dense
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T01:20:09.504011+00:00
-- url     : https://prove2.me/submissions/5cab2d13-89f9-4b62-a2e0-148f35753771

import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.IntermediateValue

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

lemma local_planar_simple_arc_complement_dense (a : ℝ → ℝ × ℝ)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hinj : InjOn a (Icc (0 : ℝ) 1)) :
    Dense (a '' Icc (0 : ℝ) 1)ᶜ := by
  have hrank : 1 < Module.rank ℝ (ℝ × ℝ) := by
    simpa only [rank_prod', Module.rank_self, one_add_one_eq_two] using Cardinal.one_lt_two
  exact dense_compl_compact_injOn_real_image hrank _ a isCompact_Icc ha hinj


theorem solution (a : ℝ → ℝ × ℝ)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hinj : InjOn a (Icc (0 : ℝ) 1)) :
    Dense (a '' Icc (0 : ℝ) 1)ᶜ :=
  local_planar_simple_arc_complement_dense a ha hinj
