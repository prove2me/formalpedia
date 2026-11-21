-- Prove2me | solution 1 for isN_of_not_dacey
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T15:11:25.823013+00:00
-- url     : https://prove2.me/submissions/17ac9576-70ae-4924-9713-92e9a1893b2a

import Mathlib
import Definitions.Def_Basic
import Theorems.Thm_perp_iff
import Theorems.Thm_chardacey
import Theorems.Thm_updown
attribute [local simp] perp_iff

set_option autoImplicit true
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]
theorem _root_.solution [Finite P] (hD : ¬ IsDacey P) :
    ∃ a b c d : P, IsN a b c d := by
  haveI : Fintype P := Fintype.ofFinite P
  haveI : DecidableRel (α := P) (· ≤ ·) := fun _ _ => Classical.dec _
  haveI : DecidableRel (α := P) (· < ·) := fun _ _ => Classical.dec _
  haveI : LocallyFiniteOrder P := Fintype.toLocallyFiniteOrder
  -- Step 1: extract non-Dacey X, basis B, and c ∈ B⊥ \ X⊥
  simp only [IsDacey] at hD
  push Not at hD
  obtain ⟨X, hX, hXnotD⟩ := hD
  rw [chardacey hX] at hXnotD
  push Not at hXnotD
  obtain ⟨B, hB, hnotSub⟩ := hXnotD
  obtain ⟨c, hcB, hcXp⟩ := Set.not_subset.mp hnotSub
  -- Step 2: c ∉ X (c ⊥ B and B is maximal orthogonal in X)
  have hcX : c ∉ X := by
    intro hcXmem
    have hcBmem : c ∈ B := hB.2.2 c hcXmem
      (fun b hb => Orthoset.perp_symm (hcB b hb))
    exact Orthoset.perp_irrefl c (hcB c hcBmem)
  -- Step 3: c ∉ X ∪ X⊥, apply updown
  have hcnotXXp : c ∉ X ∪ orthComp X := by simp [Set.mem_union, hcX, hcXp]
  obtain ⟨x, hxX, y, hyXp, hdir⟩ :=
    ((updown X (orthComp X)).mp ⟨hX, rfl⟩).2 c hcnotXXp
  -- Step 4: case split — c below both x,y or above both
  rcases hdir with ⟨hcx, hcy⟩ | ⟨hxc, hyc⟩
  · -- D_X case: c < x ∈ X and c < y ∈ X⊥
    haveI : DecidablePred (· ∈ X) := fun _ => Classical.dec _
    haveI : DecidablePred (· ∈ orthComp X) := fun _ => Classical.dec _
    haveI : DecidablePred (· ∈ orthComp B) := fun _ => Classical.dec _
    haveI : DecidablePred (fun z : P =>
        z ∈ orthComp B ∧
        ∃ x' ∈ Finset.univ.filter (· ∈ X),
        ∃ y' ∈ Finset.univ.filter (· ∈ orthComp X), z < x' ∧ z < y') :=
      fun _ => Classical.dec _
    -- D_X ∩ B⊥ as a Finset; nonempty since c ∈ it
    let DXB : Finset P := Finset.univ.filter (fun z =>
      z ∈ orthComp B ∧
      ∃ x' ∈ Finset.univ.filter (· ∈ X),
      ∃ y' ∈ Finset.univ.filter (· ∈ orthComp X), z < x' ∧ z < y')
    have hDXBne : DXB.Nonempty :=
      ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hcB, x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxX⟩,
              y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyXp⟩, hcx, hcy⟩⟩
    -- Take c' maximal in DXB
    obtain ⟨c', hc'DXB, hc'max⟩ := DXB.exists_maximal hDXBne
    obtain ⟨-, hc'B, x', hx'X, y', hy'Xp, hc'x', hc'y'⟩ :=
      Finset.mem_filter.mp hc'DXB
    rw [Finset.mem_filter] at hx'X hy'Xp
    simp only [Finset.mem_univ, true_and] at hx'X hy'Xp
    -- Take b minimal in (c', x'] = {w | c' < w ∧ w ≤ x'}
    let Icx : Finset P := Finset.univ.filter (fun w => c' < w ∧ w ≤ x')
    have hIcxne : Icx.Nonempty :=
      ⟨x', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc'x', le_refl _⟩⟩
    obtain ⟨b, hbIcx, hbmin⟩ := Icx.exists_minimal hIcxne
    obtain ⟨-, hc'b, hbx'⟩ := Finset.mem_filter.mp hbIcx
    -- c' ⋖ b
    have hcov : c' ⋖ b :=
      ⟨hc'b, fun z hc'z hzb => lt_irrefl z (hzb.trans_le (hbmin
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc'z, hzb.le.trans hbx'⟩)
        hzb.le))⟩
    -- Case split: b ∈ X or b ∉ X
    by_cases hbX : b ∈ X
    · -- b ∈ X: find d ∈ B with d < b; then N(d, c', b, y')
      -- b ∉ B: if b ∈ B then b ⊥ c' giving ¬ c' ≤ b, contradicting hcov
      have hbnotB : b ∉ B := fun hbB => (hc'B b hbB).2 hcov.le
      -- b ⊬ B: maximality gives ∃ d ∈ B, ¬ b ⊥ d
      obtain ⟨d, hdB, hbnd⟩ : ∃ d ∈ B, ¬ b ⊥ d := by
        have h : ¬ (∀ w ∈ B, b ⊥ w) := fun h => hbnotB (hB.2.2 b hbX h)
        push Not at h; exact h
      simp only [perp_iff, not_and_or, not_not] at hbnd
      rcases hbnd with hbd | hdb
      · -- b ≤ d: b < d (b ≠ d) gives c' < d contradicting d ⊥ c'
        have hbdlt : b < d := hbd.lt_of_ne (fun heq => hbnotB (heq ▸ hdB))
        exact absurd (hcov.lt.trans hbdlt).le (hc'B d hdB).2
      · -- d ≤ b: strengthen to d < b (d = b contradicts b ∉ B); N(d, c', b, y')
        have hdblt : d < b := hdb.lt_of_ne (fun heq => hbnotB (heq.symm ▸ hdB))
        exact ⟨d, c', b, y', hdblt, hcov, hc'y',
               hc'B d hdB, hy'Xp d (hB.1 hdB), hy'Xp b hbX⟩
    · -- b ∉ X: b ∉ X⊥ (b ≤ x'), b ∈ D_X; b ∉ B⊥ (maximality); find w ∈ B, w < b; N(w, c', b, y')
      have hbXp : b ∉ orthComp X := fun h => (h x' hx'X).2 hbx'
      have hbnotXXp : b ∉ X ∪ orthComp X := by simp [Set.mem_union, hbX, hbXp]
      have hbxlt : b < x' := hbx'.lt_of_ne (fun heq => hbX (heq ▸ hx'X))
      obtain ⟨z_y, hz_yXp, hz_yb⟩ : ∃ z ∈ orthComp X, b < z := by
        obtain ⟨_, _, v, hvXp, hdir⟩ :=
          ((updown X (orthComp X)).mp ⟨hX, rfl⟩).2 b hbnotXXp
        rcases hdir with ⟨-, hbv⟩ | ⟨-, hvb⟩
        · exact ⟨v, hvXp, hbv⟩
        · exact absurd (hvb.trans hbxlt).le (hvXp x' hx'X).2
      have hbDX : ∃ u ∈ Finset.univ.filter (· ∈ X),
                  ∃ v ∈ Finset.univ.filter (· ∈ orthComp X), b < u ∧ b < v :=
        ⟨x', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'X⟩,
         z_y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz_yXp⟩, hbxlt, hz_yb⟩
      have hbnotBp : b ∉ orthComp B := fun hbBp =>
        lt_irrefl c' (hcov.lt.trans_le (hc'max
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbBp, hbDX⟩) hcov.le))
      obtain ⟨w, hwB, hbw⟩ : ∃ w ∈ B, ¬ b ⊥ w := by
        have h : ¬ (∀ w ∈ B, w ⊥ b) := hbnotBp
        push Not at h
        obtain ⟨w, hwB, hwb⟩ := h
        exact ⟨w, hwB, fun hbw => hwb (Orthoset.perp_symm hbw)⟩
      simp only [perp_iff, not_and_or, not_not] at hbw
      rcases hbw with hbd | hdb
      · -- b ≤ w: b < w (b ∉ X but w ∈ X) gives c' < w contradicting w ⊥ c'
        have hbwlt : b < w := hbd.lt_of_ne (fun heq => hbX (hB.1 (heq ▸ hwB)))
        exact absurd (hcov.lt.trans hbwlt).le (hc'B w hwB).2
      · -- w ≤ b: strengthen to w < b; b ⊥ y' via w < b (for ¬ b ≤ y') and c' ⋖ b (for ¬ y' ≤ b)
        have hwblt : w < b := hdb.lt_of_ne (fun heq => hbX (hB.1 (heq.symm ▸ hwB)))
        have hby' : b ⊥ y' :=
          ⟨fun hby' => (hy'Xp w (hB.1 hwB)).1 (hwblt.le.trans hby'),
           fun hy'b => hcov.2 hc'y' (hy'b.lt_of_ne (fun heq => hbXp (heq ▸ hy'Xp)))⟩
        exact ⟨w, c', b, y', hwblt, hcov, hc'y',
               hc'B w hwB, hy'Xp w (hB.1 hwB), hby'⟩
  · -- U_X case: x < c (x ∈ X) and y < c (y ∈ X⊥)
    haveI : DecidablePred (· ∈ X) := fun _ => Classical.dec _
    haveI : DecidablePred (· ∈ orthComp X) := fun _ => Classical.dec _
    haveI : DecidablePred (· ∈ orthComp B) := fun _ => Classical.dec _
    -- Step 5: take c' minimal in U_X ∩ B⊥ (it contains c)
    haveI : DecidablePred (fun z : P =>
        z ∈ orthComp B ∧
        ∃ x' ∈ Finset.univ.filter (· ∈ X),
        ∃ y' ∈ Finset.univ.filter (· ∈ orthComp X), x' < z ∧ y' < z) :=
      fun _ => Classical.dec _
    let UXB : Finset P := Finset.univ.filter (fun z =>
      z ∈ orthComp B ∧
      ∃ x' ∈ Finset.univ.filter (· ∈ X),
      ∃ y' ∈ Finset.univ.filter (· ∈ orthComp X), x' < z ∧ y' < z)
    have hUXBne : UXB.Nonempty :=
      ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hcB, x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxX⟩,
              y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyXp⟩, hxc, hyc⟩⟩
    obtain ⟨c', hc'UXB, hc'min⟩ := UXB.exists_minimal hUXBne
    obtain ⟨-, hc'B, x', hx'X, y', hy'Xp, hx'c', hy'c'⟩ :=
      Finset.mem_filter.mp hc'UXB
    rw [Finset.mem_filter] at hx'X hy'Xp
    simp only [Finset.mem_univ, true_and] at hx'X hy'Xp
    -- Step 6: take b maximal in [x', c'); then b ⋖ c'
    let Ixc : Finset P := Finset.univ.filter (fun w => x' ≤ w ∧ w < c')
    have hIxcne : Ixc.Nonempty :=
      ⟨x', Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl _, hx'c'⟩⟩
    obtain ⟨b, hbIxc, hbmax⟩ := Ixc.exists_maximal hIxcne
    obtain ⟨-, hx'b, hbc'⟩ := Finset.mem_filter.mp hbIxc
    have hcov : b ⋖ c' :=
      ⟨hbc', fun z hbz hzc' => lt_irrefl b (hbz.trans_le (hbmax
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'b.trans hbz.le, hzc'⟩)
        hbz.le))⟩
    -- Step 7: case split b ∈ X or b ∉ X
    by_cases hbX : b ∈ X
    · -- b ∈ X: find d ∈ B with b < d; then N(y', b, c', d)
      -- b ∉ B: if b ∈ B then b ⊥ c' (since c' ∈ B⊥), giving ¬ b ≤ c', contradicting hcov
      have hbnotB : b ∉ B := fun hbB => (hc'B b hbB).1 hcov.le
      -- b ⊬ B: B is a maximal orthogonal set in X; b ∈ X and b ∉ B implies ∃ d ∈ B, ¬ b ⊥ d
      obtain ⟨d, hdB, hbnd⟩ : ∃ d ∈ B, ¬ b ⊥ d := by
        have h : ¬ (∀ w ∈ B, b ⊥ w) := fun h => hbnotB (hB.2.2 b hbX h)
        push Not at h; exact h
      simp only [perp_iff, not_and_or, not_not] at hbnd
      rcases hbnd with hbd | hdb
      · -- b ≤ d: strengthen to b < d (b = d gives d ≤ c' contradicting d ⊥ c')
        have hbdlt : b < d := hbd.lt_of_ne (fun heq => (hc'B d hdB).1 (heq ▸ hcov.le))
        exact ⟨y', b, c', d, hy'c', hcov, hbdlt,
               Orthoset.perp_symm (hy'Xp b hbX),
               Orthoset.perp_symm (hy'Xp d (hB.1 hdB)),
               Orthoset.perp_symm (hc'B d hdB)⟩
      · -- d ≤ b: d ≤ b < c' contradicts d ⊥ c' (d ∈ B, c' ∈ B⊥)
        exact absurd (hdb.trans hcov.le) (hc'B d hdB).1
    · -- b ∉ X: b ∉ X⊥ (x' ≤ b), b ∈ U_X; b ∉ B⊥ (minimality); find w ∈ B, b < w; N(y', b, c', w)
      -- x' ≤ b and x' ∈ X, so b ∉ X⊥ (else x' ⊥ b giving ¬ x' ≤ b)
      have hbXp : b ∉ orthComp X := fun h => (h x' hx'X).1 hx'b
      have hbnotXXp : b ∉ X ∪ orthComp X := by simp [Set.mem_union, hbX, hbXp]
      have hx'blt : x' < b := hx'b.lt_of_ne (fun heq => hbX (heq ▸ hx'X))
      obtain ⟨y, hyXp, hyb⟩ : ∃ y ∈ orthComp X, y < b := by
        obtain ⟨_, _, v, hvXp, hdir⟩ :=
          ((updown X (orthComp X)).mp ⟨hX, rfl⟩).2 b hbnotXXp
        rcases hdir with ⟨_, hbv⟩ | ⟨-, hvb⟩
        · exact absurd (hx'blt.trans hbv).le (hvXp x' hx'X).1
        · exact ⟨v, hvXp, hvb⟩
      -- b ∈ U_X: witnessed by x' ∈ X with x' < b and y ∈ X⊥ with y < b
      have hbUX : ∃ u ∈ Finset.univ.filter (· ∈ X),
                  ∃ v ∈ Finset.univ.filter (· ∈ orthComp X), u < b ∧ v < b :=
        ⟨x', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'X⟩,
         y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyXp⟩, hx'blt, hyb⟩
      -- b ∉ B⊥: if b ∈ B⊥ then b ∈ UXB, contradicting minimality of c'
      have hbnotBp : b ∉ orthComp B := fun hbBp =>
        lt_irrefl b (hcov.lt.trans_le (hc'min
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbBp, hbUX⟩) hcov.le))
      obtain ⟨w, hwB, hbw⟩ : ∃ w ∈ B, ¬ b ⊥ w := by
        have h : ¬ (∀ w ∈ B, w ⊥ b) := hbnotBp
        push Not at h
        obtain ⟨w, hwB, hwb⟩ := h
        exact ⟨w, hwB, fun hbw => hwb (Orthoset.perp_symm hbw)⟩
      simp only [perp_iff, not_and_or, not_not] at hbw
      rcases hbw with hbw | hwb
      · -- b ≤ w: strengthen to b < w (b = w gives w ≤ c' contradicting w ⊥ c')
        have hbwlt : b < w := hbw.lt_of_ne (fun heq => (hc'B w hwB).1 (heq ▸ hcov.le))
        exact ⟨y', b, c', w, hy'c', hcov, hbwlt,
               ⟨fun hy'b => (hy'Xp w (hB.1 hwB)).2 (hy'b.trans hbwlt.le),
                fun hby' => (hy'Xp x' hx'X).1 (hx'blt.le.trans hby')⟩,
               Orthoset.perp_symm (hy'Xp w (hB.1 hwB)),
               Orthoset.perp_symm (hc'B w hwB)⟩
      · -- w ≤ b: w ≤ b < c' contradicts w ⊥ c' (w ∈ B, c' ∈ B⊥)
        exact absurd (hwb.trans hcov.le) (hc'B w hwB).1
