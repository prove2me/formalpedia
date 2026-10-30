-- Prove2me | solution 1 for planar_arc_attachment_same_component_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T02:43:01.83839+00:00
-- url     : https://prove2.me/submissions/4eb0b892-a1db-4d82-b866-1e4f50915f37
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_planar_crosscut_same_complement_component_two
import Mathlib.Data.Fintype.Sigma
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Data.Set.Card
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Connected.LocallyConnected

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


lemma connected_component_unchanged_gives_same {X : Type} [TopologicalSpace X]
    {U W : Set X} (hWU : W ⊆ U) (x y : W)
    (hxy : y.1 ∈ connectedComponentIn U x.1)
    (hsub : connectedComponentIn U x.1 ⊆ W) :
    ConnectedComponents.mk x = ConnectedComponents.mk y := by
  symm
  apply (component_mk_eq_iff y x).mpr
  exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn (hWU x.2)) hsub hxy


lemma induced_map_unique_of_component_subset {X : Type} [TopologicalSpace X]
    {U W : Set X} (hWU : W ⊆ U) (x : U)
    (hsub : connectedComponentIn U x.1 ⊆ W) :
    ∃! c : ConnectedComponents W,
      inducedComponentMap hWU c = ConnectedComponents.mk x := by
  have hxW : x.1 ∈ W := hsub (mem_connectedComponentIn x.2)
  let x' : W := ⟨x.1, hxW⟩
  refine ⟨ConnectedComponents.mk x', ?_, ?_⟩
  · change ConnectedComponents.mk (Set.inclusion hWU x') = ConnectedComponents.mk x
    congr 1
  · intro c hc
    obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [inducedComponentMap_mk] at hc
    have hy : y.1 ∈ connectedComponentIn U x.1 :=
      (component_mk_eq_iff (Set.inclusion hWU y) x).mp hc
    exact (connected_component_unchanged_gives_same hWU x' y hy hsub).symm


lemma card_one_exception {X Y : Type} [Fintype X] [Fintype Y]
    (f : X → Y) (y₀ : Y) (h : ∀ y, y ≠ y₀ → ∃! x, f x = y) :
    Nat.card X + 1 = Nat.card Y + Nat.card {x // f x = y₀} := by
  classical
  let g : {x // f x ≠ y₀} → {y // y ≠ y₀} := fun x ↦ ⟨f x.1, x.2⟩
  have hgi : Function.Injective g := by
    intro x z heq
    have hval : f x.1 = f z.1 := congrArg Subtype.val heq
    obtain ⟨w, hw, hunique⟩ := h (f x.1) x.2
    apply Subtype.ext
    exact (hunique x.1 rfl).trans (hunique z.1 hval.symm).symm
  have hgs : Function.Surjective g := by
    intro y
    obtain ⟨x, hx, _⟩ := h y.1 y.2
    have hne : f x ≠ y₀ := hx ▸ y.2
    exact ⟨⟨x, hne⟩, Subtype.ext hx⟩
  let e : {x // f x ≠ y₀} ≃ {y // y ≠ y₀} := Equiv.ofBijective g ⟨hgi, hgs⟩
  have hX : Fintype.card X = Fintype.card {x // f x = y₀} +
      Fintype.card {x // f x ≠ y₀} := by
    simpa only [Fintype.card_sum] using
      (Fintype.card_congr (Equiv.sumCompl (fun x ↦ f x = y₀))).symm
  have hY : Fintype.card Y = Fintype.card {y // y ≠ y₀} + 1 := by
    simpa only [Fintype.card_option] using
      (Fintype.card_congr (Equiv.optionSubtypeNe y₀)).symm
  have he : Fintype.card {x // f x ≠ y₀} = Fintype.card {y // y ≠ y₀} :=
    Fintype.card_congr e
  simp only [Nat.card_eq_fintype_card]
  omega


lemma component_count_one_exception {X : Type} [TopologicalSpace X]
    {U W : Set X} (hWU : W ⊆ U) [Finite (ConnectedComponents U)]
    [Finite (ConnectedComponents W)] (c₀ : ConnectedComponents U)
    (hkeep : ∀ x : U, ConnectedComponents.mk x ≠ c₀ → connectedComponentIn U x.1 ⊆ W) :
    Nat.card (ConnectedComponents W) + 1 =
      Nat.card (ConnectedComponents U) +
        Nat.card {c : ConnectedComponents W // inducedComponentMap hWU c = c₀} := by
  classical
  let : Fintype (ConnectedComponents U) := Fintype.ofFinite _
  let : Fintype (ConnectedComponents W) := Fintype.ofFinite _
  apply card_one_exception (inducedComponentMap hWU) c₀
  intro c hc
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  exact induced_map_unique_of_component_subset hWU x (hkeep x hc)



open Set

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

lemma attaching_compact_arc {X : Type} [TopologicalSpace X] (K : Set X) (a : ℝ → X)
    (hK : IsCompact K) (ha : ContinuousOn a (Set.Icc (0 : ℝ) 1)) :
    IsCompact (K ∪ a '' Set.Icc (0 : ℝ) 1) :=
  hK.union (isCompact_Icc.image_of_continuousOn ha)

lemma arc_endpoints_ne {X : Type} (a : ℝ → X)
    (ha : Set.InjOn a (Set.Icc (0 : ℝ) 1)) : a 0 ≠ a 1 := by
  intro h
  have h01 : (0 : ℝ) = 1 := ha ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ h
  exact zero_ne_one h01


lemma interior_component {X : Type} [TopologicalSpace X] (K : Set X) (a : ℝ → X)
    (hc : ContinuousOn a (Set.Icc (0 : ℝ) 1))
    (hout : ∀ t ∈ Set.Ioo (0 : ℝ) 1, a t ∉ K)
    (s t : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    a t ∈ connectedComponentIn Kᶜ (a s) := by
  have hpre : IsPreconnected (a '' Set.Ioo (0 : ℝ) 1) :=
    isPreconnected_Ioo.image a (hc.mono Set.Ioo_subset_Icc_self)
  have hsubset : a '' Set.Ioo (0 : ℝ) 1 ⊆ Kᶜ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hout x hx
  exact hpre.subset_connectedComponentIn ⟨s, hs, rfl⟩ hsubset ⟨t, ht, rfl⟩


lemma untouched_component {X : Type} [TopologicalSpace X] (K T : Set X) (x : X)
    (hx : x ∈ Kᶜ) (hd : Disjoint (connectedComponentIn Kᶜ x) T) :
    connectedComponentIn (K ∪ T)ᶜ x = connectedComponentIn Kᶜ x := by
  apply Set.Subset.antisymm
  · apply connectedComponentIn_mono x
    intro y hy
    exact fun hyK ↦ hy (Or.inl hyK)
  · have hsub : connectedComponentIn Kᶜ x ⊆ (K ∪ T)ᶜ := by
      intro y hy hyUnion
      rcases hyUnion with hyK | hyT
      · exact (connectedComponentIn_subset Kᶜ x hy) hyK
      · exact Set.disjoint_left.mp hd hy hyT
    exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hx) hsub


lemma unvisited_component_unchanged {X : Type} [TopologicalSpace X] (K : Set X)
    (a : ℝ → X) (hc : ContinuousOn a (Set.Icc (0 : ℝ) 1))
    (hzero : a 0 ∈ K) (hone : a 1 ∈ K)
    (hout : ∀ t ∈ Set.Ioo (0 : ℝ) 1, a t ∉ K)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    (x : X) (hx : x ∈ Kᶜ) (hmiss : a s ∉ connectedComponentIn Kᶜ x) :
    connectedComponentIn (K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ x = connectedComponentIn Kᶜ x := by
  apply untouched_component K (a '' Set.Icc (0 : ℝ) 1) x hx
  apply Set.disjoint_left.mpr
  intro z hzC hzA
  obtain ⟨t, ht, rfl⟩ := hzA
  have hzK : a t ∉ K := connectedComponentIn_subset Kᶜ x hzC
  have h0 : t ≠ 0 := by
    intro ht0
    subst t
    exact hzK hzero
  have h1 : t ≠ 1 := by
    intro ht1
    subst t
    exact hzK hone
  have ht' : t ∈ Set.Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩
  have hsC : a s ∈ connectedComponentIn Kᶜ (a t) :=
    interior_component K a hc hout t s ht' hs
  rw [← connectedComponentIn_eq hzC] at hsC
  exact hmiss hsC


lemma arc_component_count_conditional {X : Type} [TopologicalSpace X] (K : Set X)
    (a : ℝ → X) (hc : ContinuousOn a (Set.Icc (0 : ℝ) 1))
    (hzero : a 0 ∈ K) (hone : a 1 ∈ K)
    (hout : ∀ t ∈ Set.Ioo (0 : ℝ) 1, a t ∉ K)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    [Finite (ConnectedComponents (Kᶜ : Set X))]
    [Finite (ConnectedComponents ((K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ : Set X))] :
    let hWU : (K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ ⊆ Kᶜ :=
      fun _ hz hK ↦ hz (Or.inl hK)
    let c₀ : ConnectedComponents (Kᶜ : Set X) := ConnectedComponents.mk ⟨a s, hout s hs⟩
    Nat.card (ConnectedComponents ((K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ : Set X)) + 1 =
      Nat.card (ConnectedComponents (Kᶜ : Set X)) +
        Nat.card {c : ConnectedComponents ((K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ : Set X) //
          inducedComponentMap hWU c = c₀} := by
  dsimp only
  apply component_count_one_exception
  intro x hx
  have hmiss : a s ∉ connectedComponentIn Kᶜ x.1 := by
    intro hmem
    apply hx
    apply (component_mk_eq_iff x ⟨a s, hout s hs⟩).mpr
    rw [← connectedComponentIn_eq hmem]
    exact mem_connectedComponentIn x.2
  have heq := unvisited_component_unchanged K a hc hzero hone hout s hs x.1 x.2 hmiss
  rw [← heq]
  exact connectedComponentIn_subset _ _


lemma finite_one_exception {X Y : Type} [Finite Y] (f : X → Y) (y₀ : Y)
    [Finite {x // f x = y₀}]
    (h : ∀ y, y ≠ y₀ → ∀ x x', f x = y → f x' = y → x = x') : Finite X := by
  classical
  have hf : ∀ y : Y, Finite {x // f x = y} := by
    intro y
    by_cases hy : y = y₀
    · subst y
      infer_instance
    · have hsub : Subsingleton {x // f x = y} := by
        constructor
        intro x x'
        exact Subtype.ext (h y hy x.1 x'.1 x.2 x'.2)
      let : Subsingleton {x // f x = y} := hsub
      infer_instance
  letI : Fintype Y := Fintype.ofFinite Y
  letI (y : Y) : Fintype {x // f x = y} := @Fintype.ofFinite _ (hf y)
  exact Finite.of_equiv (Σ y : Y, {x // f x = y}) (Equiv.sigmaFiberEquiv f)


lemma component_count_one_exception_finite {X : Type} [TopologicalSpace X]
    {U W : Set X} (hWU : W ⊆ U) [Finite (ConnectedComponents U)]
    (c₀ : ConnectedComponents U)
    [Finite {c : ConnectedComponents W // inducedComponentMap hWU c = c₀}]
    (hkeep : ∀ x : U, ConnectedComponents.mk x ≠ c₀ → connectedComponentIn U x.1 ⊆ W) :
    Finite (ConnectedComponents W) ∧
      Nat.card (ConnectedComponents W) + 1 =
        Nat.card (ConnectedComponents U) +
          Nat.card {c : ConnectedComponents W // inducedComponentMap hWU c = c₀} := by
  classical
  have huniq : ∀ c : ConnectedComponents U, c ≠ c₀ →
      ∃! d : ConnectedComponents W, inducedComponentMap hWU d = c := by
    intro c hc
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    exact induced_map_unique_of_component_subset hWU x (hkeep x hc)
  have hfin : Finite (ConnectedComponents W) :=
    finite_one_exception (inducedComponentMap hWU) c₀ (by
      intro c hc x x' hx hx'
      obtain ⟨z, hz, hunique⟩ := huniq c hc
      exact (hunique x hx).trans (hunique x' hx').symm)
  let : Finite (ConnectedComponents W) := hfin
  exact ⟨hfin, component_count_one_exception hWU c₀ hkeep⟩



lemma arc_component_count_finite_reduction {X : Type} [TopologicalSpace X] (K : Set X)
    (a : ℝ → X) (hc : ContinuousOn a (Set.Icc (0 : ℝ) 1))
    (hzero : a 0 ∈ K) (hone : a 1 ∈ K)
    (hout : ∀ t ∈ Set.Ioo (0 : ℝ) 1, a t ∉ K)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    [Finite (ConnectedComponents (Kᶜ : Set X))] :
    let hWU : (K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ ⊆ Kᶜ :=
      fun _ hz hK ↦ hz (Or.inl hK)
    let c₀ : ConnectedComponents (Kᶜ : Set X) := ConnectedComponents.mk ⟨a s, hout s hs⟩
    Finite {c : ConnectedComponents ((K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ : Set X) //
        inducedComponentMap hWU c = c₀} →
      Finite (ConnectedComponents ((K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ : Set X)) ∧
        Nat.card (ConnectedComponents ((K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ : Set X)) + 1 =
          Nat.card (ConnectedComponents (Kᶜ : Set X)) +
            Nat.card {c : ConnectedComponents ((K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ : Set X) //
              inducedComponentMap hWU c = c₀} := by
  dsimp only
  intro hfinite
  letI := hfinite
  apply component_count_one_exception_finite
  intro x hx
  have hmiss : a s ∉ connectedComponentIn Kᶜ x.1 := by
    intro hmem
    apply hx
    apply (component_mk_eq_iff x ⟨a s, hout s hs⟩).mpr
    rw [← connectedComponentIn_eq hmem]
    exact mem_connectedComponentIn x.2
  have heq := unvisited_component_unchanged K a hc hzero hone hout s hs x.1 x.2 hmiss
  rw [← heq]
  exact connectedComponentIn_subset _ _


lemma saturated_component {Z : Type} [TopologicalSpace Z] (P : Set Z)
    (hP : ∀ x ∈ P, connectedComponent x ⊆ P) (x : Z) (hx : x ∈ P) :
    connectedComponentIn P x = connectedComponent x := by
  apply Set.Subset.antisymm
  · exact isPreconnected_connectedComponentIn.subset_connectedComponent (mem_connectedComponentIn hx)
  · exact isPreconnected_connectedComponent.subset_connectedComponentIn mem_connectedComponent (hP x hx)

lemma saturated_subtype_relation {Z : Type} [TopologicalSpace Z] (P : Set Z)
    (hP : ∀ x ∈ P, connectedComponent x ⊆ P) (x y : P) :
    connectedComponent x = connectedComponent y ↔
      connectedComponent x.1 = connectedComponent y.1 := by
  rw [← ConnectedComponents.coe_eq_coe]
  rw [component_mk_eq_iff, saturated_component P hP y.1 y.2]
  exact connectedComponent_eq_iff_mem.symm

noncomputable def saturated_components_equiv {Z : Type} [TopologicalSpace Z] (P : Set Z)
    (Q : ConnectedComponents Z → Prop)
    (hP : ∀ x ∈ P, connectedComponent x ⊆ P)
    (hQ : ∀ x : Z, x ∈ P ↔ Q (ConnectedComponents.mk x)) :
    {c : ConnectedComponents Z // Q c} ≃ ConnectedComponents P :=
  Equiv.subtypeQuotientEquivQuotientSubtype (· ∈ P) Q hQ
    (fun x y ↦ saturated_subtype_relation P hP x y)


noncomputable def component_fiber_equiv {X : Type} [TopologicalSpace X]
    {U W : Set X} (hWU : W ⊆ U) (x₀ : U) :
    {c : ConnectedComponents W // inducedComponentMap hWU c = ConnectedComponents.mk x₀} ≃
      ConnectedComponents {w : W // Set.inclusion hWU w ∈ connectedComponent x₀} := by
  let P : Set W := {w | Set.inclusion hWU w ∈ connectedComponent x₀}
  have hP : ∀ w ∈ P, connectedComponent w ⊆ P := by
    intro w hw z hz
    have hmap := (continuous_inclusion hWU).mapsTo_connectedComponent w hz
    have heq : connectedComponent (Set.inclusion hWU w) = connectedComponent x₀ :=
      (connectedComponent_eq hw).symm
    rw [heq] at hmap
    exact hmap
  have hQ : ∀ w : W, w ∈ P ↔
      inducedComponentMap hWU (ConnectedComponents.mk w) = ConnectedComponents.mk x₀ := by
    intro w
    change Set.inclusion hWU w ∈ connectedComponent x₀ ↔ _
    rw [inducedComponentMap_mk, ConnectedComponents.coe_eq_coe']
  exact saturated_components_equiv P
    (fun c ↦ inducedComponentMap hWU c = ConnectedComponents.mk x₀) hP hQ



lemma arc_local_component_reduction {X : Type} [TopologicalSpace X] (K : Set X)
    (a : ℝ → X) (hc : ContinuousOn a (Set.Icc (0 : ℝ) 1))
    (hzero : a 0 ∈ K) (hone : a 1 ∈ K)
    (hout : ∀ t ∈ Set.Ioo (0 : ℝ) 1, a t ∉ K)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1)
    [Finite (ConnectedComponents (Kᶜ : Set X))] :
    let hWU : (K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ ⊆ Kᶜ :=
      fun _ hz hK ↦ hz (Or.inl hK)
    let x₀ : (Kᶜ : Set X) := ⟨a s, hout s hs⟩
    let R := {w : ((K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ : Set X) //
      Set.inclusion hWU w ∈ connectedComponent x₀}
    Finite (ConnectedComponents R) →
      Finite (ConnectedComponents ((K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ : Set X)) ∧
        Nat.card (ConnectedComponents ((K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ : Set X)) + 1 =
          Nat.card (ConnectedComponents (Kᶜ : Set X)) + Nat.card (ConnectedComponents R) := by
  dsimp only
  intro hR
  let hWU : (K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ ⊆ Kᶜ := fun _ hz hK ↦ hz (Or.inl hK)
  let x₀ : (Kᶜ : Set X) := ⟨a s, hout s hs⟩
  let e := component_fiber_equiv hWU x₀
  have hfiber : Finite {c : ConnectedComponents ((K ∪ a '' Set.Icc (0 : ℝ) 1)ᶜ : Set X) //
      inducedComponentMap hWU c = ConnectedComponents.mk x₀} := by
    letI := hR
    exact Finite.of_equiv _ e.symm
  have hmain := arc_component_count_finite_reduction K a hc hzero hone hout s hs hfiber
  constructor
  · exact hmain.1
  · rw [hmain.2]
    exact congrArg (Nat.card (ConnectedComponents (Kᶜ : Set X)) + ·) (Nat.card_congr e)

open Set

/-- Membership in a component of a subspace agrees with component membership
in the ambient space relative to that subspace. -/
lemma mem_connectedComponentIn_iff_subtype
    {X : Type} [TopologicalSpace X] (U : Set X) (x y : U) :
    y.1 ∈ connectedComponentIn U x.1 ↔ y ∈ connectedComponent x := by
  rw [connectedComponentIn_eq_image x.2]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hzy' : z = y := Subtype.ext hzy
    simpa only [hzy'] using hz
  · intro hy
    exact ⟨y, hy, rfl⟩

/-- The local exceptional fiber used in the counting argument is homeomorphic
to the ambient intersection of the smaller set with the old component. -/
noncomputable def localComponentHomeomorph
    {X : Type} [TopologicalSpace X] (U W : Set X) (hWU : W ⊆ U) (x : U) :
    {w : W // Set.inclusion hWU w ∈ connectedComponent x} ≃ₜ
      (W ∩ connectedComponentIn U x.1 : Set X) where
  toFun := fun w => ⟨w.1.1, w.1.2,
    (mem_connectedComponentIn_iff_subtype U x (Set.inclusion hWU w.1)).mpr w.2⟩
  invFun := fun z => ⟨⟨z.1, z.2.1⟩,
    (mem_connectedComponentIn_iff_subtype U x ⟨z.1, hWU z.2.1⟩).mp z.2.2⟩
  left_inv := by intro w; apply Subtype.ext; apply Subtype.ext; rfl
  right_inv := by intro z; apply Subtype.ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Homeomorphic spaces have equivalent connected-component types. -/
noncomputable def homeomorphConnectedComponentsEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) :
    ConnectedComponents X ≃ ConnectedComponents Y :=
  Quotient.congr e.toEquiv (by
    intro x y
    change connectedComponent x = connectedComponent y ↔
      connectedComponent (e x) = connectedComponent (e y)
    rw [connectedComponent_eq_iff_mem, connectedComponent_eq_iff_mem]
    constructor
    · intro h
      exact e.continuous.mapsTo_connectedComponent y h
    · intro h
      have hh := e.symm.continuous.mapsTo_connectedComponent (e y) h
      simpa only [e.symm_apply_apply] using hh)


/-- The local fiber in the arc count is equivalent to the components of the
old region after deleting the arc. -/
noncomputable def arcLocalComponentsEquiv
    {X : Type} [TopologicalSpace X] (K : Set X) (a : ℝ → X)
    (hout : ∀ t ∈ Ioo (0 : ℝ) 1, a t ∉ K)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
    let hWU : (K ∪ a '' Icc (0 : ℝ) 1)ᶜ ⊆ Kᶜ := fun _ hz hK => hz (Or.inl hK)
    let x₀ : (Kᶜ : Set X) := ⟨a s, hout s hs⟩
    let R := {w : ((K ∪ a '' Icc (0 : ℝ) 1)ᶜ : Set X) //
      Set.inclusion hWU w ∈ connectedComponent x₀}
    ConnectedComponents R ≃
      ConnectedComponents (((connectedComponentIn Kᶜ (a s)) \ (a '' Icc (0 : ℝ) 1)) : Set X) := by
  dsimp only
  let W : Set X := (K ∪ a '' Icc (0 : ℝ) 1)ᶜ
  let U : Set X := Kᶜ
  let hWU : W ⊆ U := fun _ hz hK => hz (Or.inl hK)
  let x₀ : U := ⟨a s, hout s hs⟩
  have hset : W ∩ connectedComponentIn U x₀.1 =
      (connectedComponentIn Kᶜ (a s)) \ (a '' Icc (0 : ℝ) 1) := by
    ext z
    constructor
    · rintro ⟨hzW, hzC⟩
      exact ⟨hzC, fun hzA => hzW (Or.inr hzA)⟩
    · rintro ⟨hzC, hzA⟩
      refine ⟨?_, hzC⟩
      intro hzUnion
      rcases hzUnion with hzK | hzArc
      · exact (connectedComponentIn_subset U x₀.1 hzC) hzK
      · exact hzA hzArc
  exact homeomorphConnectedComponentsEquiv
    ((localComponentHomeomorph U W hWU x₀).trans (Homeomorph.setCongr hset))


/-- If the touched region has exactly two components after removing the arc,
then the total complement count rises by one. -/
lemma same_arc_count_of_local_two
    {X : Type} [TopologicalSpace X] (K : Set X) (a : ℝ → X)
    (hc : ContinuousOn a (Icc (0 : ℝ) 1)) (hzero : a 0 ∈ K) (hone : a 1 ∈ K)
    (hout : ∀ t ∈ Ioo (0 : ℝ) 1, a t ∉ K)
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1)
    (hfinite : Finite (ConnectedComponents (Kᶜ : Set X)))
    (hlocal : Finite (ConnectedComponents (((connectedComponentIn Kᶜ (a s)) \ (a '' Icc (0 : ℝ) 1)) : Set X)) ∧
      Nat.card (ConnectedComponents (((connectedComponentIn Kᶜ (a s)) \ (a '' Icc (0 : ℝ) 1)) : Set X)) = 2) :
    Finite (ConnectedComponents ((K ∪ a '' Icc (0 : ℝ) 1)ᶜ : Set X)) ∧
      Nat.card (ConnectedComponents ((K ∪ a '' Icc (0 : ℝ) 1)ᶜ : Set X)) =
        Nat.card (ConnectedComponents (Kᶜ : Set X)) + 1 := by
  let e := arcLocalComponentsEquiv K a hout s hs
  letI := hlocal.1
  have hRfinite : Finite _ := Finite.of_equiv _ e.symm
  letI := hfinite
  have hmain := arc_local_component_reduction K a hc hzero hone hout s hs hRfinite
  have hcR : Nat.card _ = 2 := (Nat.card_congr e).trans hlocal.2
  constructor
  · exact hmain.1
  · omega

open Set

lemma arc_endpoints_on_component_frontier {X : Type} [TopologicalSpace X] (K : Set X)
    (a : ℝ → X) (hc : ContinuousOn a (Set.Icc (0 : ℝ) 1))
    (hzero : a 0 ∈ K) (hone : a 1 ∈ K)
    (hout : ∀ t ∈ Set.Ioo (0 : ℝ) 1, a t ∉ K)
    (s : ℝ) (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    a 0 ∈ frontier (connectedComponentIn Kᶜ (a s)) ∧
      a 1 ∈ frontier (connectedComponentIn Kᶜ (a s)) := by
  let C := connectedComponentIn Kᶜ (a s)
  have hinside : a '' Set.Ioo (0 : ℝ) 1 ⊆ C := by
    rintro z ⟨t, ht, rfl⟩
    exact interior_component K a hc hout s t hs ht
  have hcont : ContinuousOn a (closure (Set.Ioo (0 : ℝ) 1)) := by
    rw [closure_Ioo zero_ne_one]
    exact hc
  have hclosure : a '' Set.Icc (0 : ℝ) 1 ⊆ closure C := by
    rw [← closure_Ioo zero_ne_one]
    exact hcont.image_closure.trans (closure_mono hinside)
  have hzero_cl : a 0 ∈ closure C := hclosure ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have hone_cl : a 1 ∈ closure C := hclosure ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  have hC : C ⊆ Kᶜ := connectedComponentIn_subset _ _
  constructor
  · rw [frontier]
    exact ⟨hzero_cl, fun hi ↦ (hC (interior_subset hi)) hzero⟩
  · rw [frontier]
    exact ⟨hone_cl, fun hi ↦ (hC (interior_subset hi)) hone⟩


/-- The arc is a crosscut of its touched region, and its endpoints are in the
same component of that region's complement. -/
lemma same_component_arc_crosscut_data
    (K : Set (ℝ × ℝ)) (hK : IsClosed K) (a : ℝ → ℝ × ℝ)
    (hc : ContinuousOn a (Icc (0 : ℝ) 1))
    (hzero : a 0 ∈ K) (hone : a 1 ∈ K)
    (hout : ∀ t ∈ Ioo (0 : ℝ) 1, a t ∉ K)
    (hsame : a 1 ∈ connectedComponentIn K (a 0))
    (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
    let U := connectedComponentIn Kᶜ (a s)
    IsOpen U ∧ IsConnected U ∧
      a '' Ioo (0 : ℝ) 1 ⊆ U ∧
      a 0 ∈ frontier U ∧ a 1 ∈ frontier U ∧
      a 1 ∈ connectedComponentIn Uᶜ (a 0) := by
  dsimp only
  let U := connectedComponentIn Kᶜ (a s)
  have hUo : IsOpen U := hK.isOpen_compl.connectedComponentIn
  have hUc : IsConnected U := isConnected_connectedComponentIn_iff.mpr (hout s hs)
  have hUi : a '' Ioo (0 : ℝ) 1 ⊆ U := by
    rintro z ⟨t, ht, rfl⟩
    exact interior_component K a hc hout s t hs ht
  have hfront := arc_endpoints_on_component_frontier K a hc hzero hone hout s hs
  have hKsub : K ⊆ Uᶜ := by
    intro z hz hzu
    exact (connectedComponentIn_subset Kᶜ (a s) hzu) hz
  have hUend : a 1 ∈ connectedComponentIn Uᶜ (a 0) :=
    connectedComponentIn_mono (a 0) hKsub hsame
  exact ⟨hUo, hUc, hUi, hfront.1, hfront.2, hUend⟩

open Set

/-- The (as yet unproved here) general planar crosscut theorem of Newman:
removing a simple crosscut whose endpoints lie in one complementary component
splits an open connected region into exactly two components. -/
def GeneralPlanarCrosscutTwo : Prop :=
  ∀ (U : Set (ℝ × ℝ)) (a : ℝ → ℝ × ℝ),
    IsOpen U → IsConnected U →
    ContinuousOn a (Icc (0 : ℝ) 1) → InjOn a (Icc (0 : ℝ) 1) →
    a '' Ioo (0 : ℝ) 1 ⊆ U → a 0 ∈ frontier U → a 1 ∈ frontier U →
    a 1 ∈ connectedComponentIn Uᶜ (a 0) →
    Finite (ConnectedComponents ((U \ (a '' Icc (0 : ℝ) 1)) : Set (ℝ × ℝ))) ∧
      Nat.card (ConnectedComponents ((U \ (a '' Icc (0 : ℝ) 1)) : Set (ℝ × ℝ))) = 2

/-- The same-component arc-attachment count follows from the general planar
crosscut theorem. The crosscut theorem is an explicit hypothesis. -/
theorem same_arc_count_of_general_crosscut
    (hcross : GeneralPlanarCrosscutTwo)
    (K : Set (ℝ × ℝ)) (a : ℝ → ℝ × ℝ)
    (hK : IsCompact K) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hinj : InjOn a (Icc (0 : ℝ) 1)) (hu : a 0 ∈ K) (hv : a 1 ∈ K)
    (hinterior : ∀ t ∈ Ioo (0 : ℝ) 1, a t ∉ K)
    (hsame : a 1 ∈ connectedComponentIn K (a 0))
    (hfinite : Finite (ConnectedComponents (Kᶜ : Set (ℝ × ℝ)))) :
    Finite (ConnectedComponents ((K ∪ a '' Icc (0 : ℝ) 1)ᶜ : Set (ℝ × ℝ))) ∧
      Nat.card (ConnectedComponents ((K ∪ a '' Icc (0 : ℝ) 1)ᶜ : Set (ℝ × ℝ))) =
        Nat.card (ConnectedComponents (Kᶜ : Set (ℝ × ℝ))) + 1 := by
  have hs : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by norm_num
  let U := connectedComponentIn Kᶜ (a (1 / 2))
  have hdata := same_component_arc_crosscut_data K hK.isClosed a ha hu hv hinterior hsame (1 / 2) hs
  have hlocal := hcross U a hdata.1 hdata.2.1 ha hinj hdata.2.2.1
    hdata.2.2.2.1 hdata.2.2.2.2.1 hdata.2.2.2.2.2
  exact same_arc_count_of_local_two K a ha hu hv hinterior (1 / 2) hs hfinite hlocal

theorem solution
    (K : Set (ℝ × ℝ)) (a : ℝ → ℝ × ℝ)
    (hK : IsCompact K) (ha : ContinuousOn a (Icc (0 : ℝ) 1))
    (hinj : InjOn a (Icc (0 : ℝ) 1)) (hu : a 0 ∈ K) (hv : a 1 ∈ K)
    (hinterior : ∀ t ∈ Ioo (0 : ℝ) 1, a t ∉ K)
    (hsame : a 1 ∈ connectedComponentIn K (a 0))
    (hfinite : Finite (ConnectedComponents (Kᶜ : Set (ℝ × ℝ)))) :
    Finite (ConnectedComponents ((K ∪ a '' Icc (0 : ℝ) 1)ᶜ : Set (ℝ × ℝ))) ∧
      Nat.card (ConnectedComponents ((K ∪ a '' Icc (0 : ℝ) 1)ᶜ : Set (ℝ × ℝ))) =
        Nat.card (ConnectedComponents (Kᶜ : Set (ℝ × ℝ))) + 1 := by
  exact same_arc_count_of_general_crosscut planar_crosscut_same_complement_component_two
    K a hK ha hinj hu hv hinterior hsame hfinite
