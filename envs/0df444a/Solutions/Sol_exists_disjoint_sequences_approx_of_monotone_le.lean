-- Prove2me | solution 1 for exists_disjoint_sequences_approx_of_monotone_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:17:48.727976+00:00
-- url     : https://prove2.me/submissions/69f2dfbc-13ac-422b-b1c8-f16dc8dbe97f

module
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_Nakano
public import Definitions.Def_LeanPool_OrderClosures_BanLat_Disjoint
public import Definitions.Def_LeanPool_OrderClosures_BanLat_OrderContinuous_MeyerNieberg
public import Theorems.Thm_IsVLDisjoint_mono_left
public import Theorems.Thm_IsVLDisjoint_smul_left
public import Theorems.Thm_IsVLDisjoint_smul_right
public import Theorems.Thm_OrderConvergesTo_sup
public import Theorems.Thm_inf_eq_zero_of_isVLDisjoint
public import Theorems.Thm_inf_le_inf_add_inf_of_nonneg
public import Theorems.Thm_isVLDisjoint_comm
public import Theorems.Thm_isVLDisjoint_finset_sum
public import Theorems.Thm_isVLDisjoint_of_inf_eq_zero
public import Theorems.Thm_isVLDisjoint_posPart_negPart
public import Theorems.Thm_posPart_smul_nonneg
public import Theorems.Thm_sub_inf_eq_posPart

section
@[expose] public section
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
section Disjointification
variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [VectorLattice E]
omit [Lattice E] [IsOrderedAddMonoid E] [VectorLattice E] in
private lemma sum_range_increments (u : ℕ → E) :
    ∀ n : ℕ, (∑ i ∈ Finset.range n, (u (i + 1) - u i)) = u n - u 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      abel
omit [VectorLattice E] in
private lemma finset_sum_increments_le_bound {x : E} {u : ℕ → E}
    (h0 : ∀ n, 0 ≤ u n) (hmono : Monotone u) (hle : ∀ n, u n ≤ x)
    (s : Finset ℕ) :
    (∑ i ∈ s, (u (i + 1) - u i)) ≤ x := by
  classical
  let N : ℕ := s.sup id + 1
  have hsub : s ⊆ Finset.range N := by
    intro i hi
    have hi_le : i ≤ s.sup id := by
      simpa using (Finset.le_sup (f := id) hi)
    simpa [N] using Nat.lt_succ_of_le hi_le
  have hnonneg : ∀ i ∈ Finset.range N, i ∉ s → 0 ≤ u (i + 1) - u i := by
    intro i _ _
    exact sub_nonneg.mpr (hmono (Nat.le_succ i))
  calc
    (∑ i ∈ s, (u (i + 1) - u i)) ≤
        ∑ i ∈ Finset.range N, (u (i + 1) - u i) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
    _ = u N - u 0 := sum_range_increments u N
    _ ≤ u N := sub_le_self _ (h0 0)
    _ ≤ x := hle N
omit [VectorLattice E] in
private lemma sum_range_mono_of_nonneg {f : ℕ → E} (hf : ∀ n, 0 ≤ f n) :
    Monotone fun n => ∑ i ∈ Finset.range n, f i := by
  intro n m hnm
  exact Finset.sum_le_sum_of_subset_of_nonneg ((Finset.range_subset_range).2 hnm)
    (fun i _ _ => hf i)
private theorem disjointification_step_one {x : E} {u : ℕ → E}
    (h0 : ∀ n, 0 ≤ u n) (hmono : Monotone u) (hle : ∀ n, u n ≤ x) (k : ℕ) :
    ∃ v : ℕ → E,
      IsKDisjointSeq (k + 1) v ∧
      (∀ n, v n ∈ Set.Icc (0 : E) x) ∧
      ∀ n, v n ≤ u (n + 1) - u n ∧
        u (n + 1) - u n ≤ v n + ((1 : ℝ) / ((k : ℝ) + 1)) • x := by
  classical
  let c : ℝ := (1 : ℝ) / ((k : ℝ) + 1)
  let d : ℕ → E := fun n => u (n + 1) - u n
  let v : ℕ → E := fun n => (d n - c • x)⁺
  have hx0 : 0 ≤ x := (h0 0).trans (hle 0)
  have hc0 : 0 ≤ c := by
    dsimp [c]
    positivity
  have hcx0 : 0 ≤ c • x := smul_nonneg hc0 hx0
  have hd0 : ∀ n, 0 ≤ d n := fun n => sub_nonneg.mpr (hmono (Nat.le_succ n))
  refine ⟨v, ?_, ?_, ?_⟩
  · intro s hcard hs
    have hv_nonneg : ∀ n, 0 ≤ v n := fun n => posPart_nonneg _
    have hv_abs : ∀ n, |v n| = v n := fun n => abs_of_nonneg (hv_nonneg n)
    rw [show s.inf' hs (fun n => |v n|) = s.inf' hs v by
      apply Finset.inf'_congr hs rfl
      intro n _
      exact hv_abs n]
    let a : E := s.inf' hs v
    let r : ℕ → E := fun n => (d n - c • x)⁻
    have ha0 : 0 ≤ a := Finset.le_inf' hs v (fun n _ => hv_nonneg n)
    have ha_le : ∀ n ∈ s, a ≤ v n := fun n hn => Finset.inf'_le v hn
    have hr_nonneg : ∀ n, 0 ≤ r n := fun n => negPart_nonneg _
    have hdisj_each : ∀ n ∈ s, IsVLDisjoint a (r n) := by
      intro n hn
      have hbase : IsVLDisjoint (v n) (r n) := by
        simpa only [v, r] using isVLDisjoint_posPart_negPart (d n - c • x)
      refine hbase.mono_left ?_
      rw [abs_of_nonneg ha0, abs_of_nonneg (hv_nonneg n)]
      exact ha_le n hn
    have hdisj_sum : IsVLDisjoint a (∑ n ∈ s, r n) :=
      isVLDisjoint_finset_sum hdisj_each
    have hmeet_zero : a ⊓ (∑ n ∈ s, r n) = 0 :=
      inf_eq_zero_of_isVLDisjoint ha0 (Finset.sum_nonneg (fun n _ => hr_nonneg n))
        hdisj_sum
    have hsumd_le : (∑ n ∈ s, d n) ≤ x :=
      finset_sum_increments_le_bound h0 hmono hle s
    have hxd_nonneg : 0 ≤ x - ∑ n ∈ s, d n := sub_nonneg.mpr hsumd_le
    have hsumv_ge : a ≤ ∑ n ∈ s, v n := by
      rcases hs with ⟨n, hn⟩
      exact (ha_le n hn).trans (Finset.single_le_sum (fun i _ => hv_nonneg i) hn)
    have hr_eq : ∀ n, r n = c • x - d n + v n := by
      intro n
      have hdec : v n - r n = d n - c • x := by
        simp [v, r, posPart_sub_negPart]
      have h1 : v n = d n - c • x + r n := sub_eq_iff_eq_add.mp hdec
      rw [h1]
      abel
    have hsumr_eq : (∑ n ∈ s, r n) = (x - ∑ n ∈ s, d n) + ∑ n ∈ s, v n := by
      calc
        (∑ n ∈ s, r n) = ∑ n ∈ s, (c • x - d n + v n) := by
          refine Finset.sum_congr rfl ?_
          intro n _
          exact hr_eq n
        _ = (∑ n ∈ s, c • x) - (∑ n ∈ s, d n) + ∑ n ∈ s, v n := by
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        _ = x - (∑ n ∈ s, d n) + ∑ n ∈ s, v n := by
          have hcard_real : (s.card : ℝ) = (k : ℝ) + 1 := by
            norm_num [hcard]
          rw [Finset.sum_const]
          rw [← Nat.cast_smul_eq_nsmul ℝ s.card (c • x)]
          rw [smul_smul, hcard_real]
          have hcoef : ((k : ℝ) + 1) * c = 1 := by
            dsimp [c]
            field_simp [show (k : ℝ) + 1 ≠ 0 by positivity]
          rw [hcoef, one_smul]
    have ha_le_sumr : a ≤ ∑ n ∈ s, r n := by
      rw [hsumr_eq]
      exact hsumv_ge.trans (le_add_of_nonneg_left hxd_nonneg)
    have ha_eq_zero : a = 0 := by
      have : a ⊓ (∑ n ∈ s, r n) = a := inf_eq_left.mpr ha_le_sumr
      exact this ▸ hmeet_zero
    exact ha_eq_zero
  · intro n
    constructor
    · exact posPart_nonneg _
    · have hv_le_d : v n ≤ d n := by
        refine sup_le ?_ (hd0 n)
        exact sub_le_self _ hcx0
      exact hv_le_d.trans ((sub_le_self _ (h0 n)).trans (hle (n + 1)))
  · intro n
    constructor
    · have hv_le_d : v n ≤ d n := by
        refine sup_le ?_ (hd0 n)
        exact sub_le_self _ hcx0
      simpa [d, v] using hv_le_d
    · have : d n ≤ v n + c • x := sub_le_iff_le_add.mp (le_posPart (d n - c • x))
      simpa [d, v, c] using this
private theorem disjointification_step_two {x : E} {u : ℕ → E} {k : ℕ}
    (hu_interval : ∀ n, u n ∈ Set.Icc (0 : E) x)
    (hu_disj : IsKDisjointSeq (k + 1) u) {eps : ℝ}
    (heps0 : 0 < eps) :
    ∃ w y : ℕ → E,
      IsKDisjointSeq k w ∧
      Pairwise (fun n m => IsVLDisjoint (y n) (y m)) ∧
      (∀ n, w n ∈ Set.Icc (0 : E) x) ∧
      (∀ n, y n ∈ Set.Icc (0 : E) x) ∧
      ∀ n, y n + w n ≤ u n ∧ u n ≤ y n + w n + eps • x := by
  classical
  let pref : ℕ → E := fun n => ∑ i ∈ Finset.range n, u i
  let inv : ℝ := eps⁻¹
  let y : ℕ → E := fun n => (u n - inv • pref n - eps • x)⁺
  let w : ℕ → E := fun n => u n ⊓ inv • pref n
  have hx0 : 0 ≤ x := (hu_interval 0).1.trans (hu_interval 0).2
  have hu0 : ∀ n, 0 ≤ u n := fun n => (hu_interval n).1
  have hux : ∀ n, u n ≤ x := fun n => (hu_interval n).2
  have heps_nonneg : 0 ≤ eps := le_of_lt heps0
  have heps_ne : eps ≠ 0 := ne_of_gt heps0
  have hinv0 : 0 ≤ inv := by
    dsimp [inv]
    exact inv_nonneg.mpr heps_nonneg
  have hpref0 : ∀ n, 0 ≤ pref n := fun n => Finset.sum_nonneg (fun i _ => hu0 i)
  have hpref_mono : Monotone pref := by
    dsimp [pref]
    exact sum_range_mono_of_nonneg hu0
  have hinvpref0 : ∀ n, 0 ≤ inv • pref n := fun n => smul_nonneg hinv0 (hpref0 n)
  have hepsx0 : 0 ≤ eps • x := smul_nonneg heps_nonneg hx0
  have hy0 : ∀ n, 0 ≤ y n := fun n => posPart_nonneg _
  refine ⟨w, y, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hcard hs
    have hw_nonneg : ∀ n, 0 ≤ w n := fun n => le_inf (hu0 n) (hinvpref0 n)
    rw [show s.inf' hs (fun n => |w n|) = s.inf' hs w by
      apply Finset.inf'_congr hs rfl
      intro n _
      exact abs_of_nonneg (hw_nonneg n)]
    let a : E := s.inf' hs w
    let b : E := s.inf' hs u
    let n0 : ℕ := s.min' hs
    have hn0_mem : n0 ∈ s := by
      simpa [n0] using Finset.min'_mem s hs
    have ha0 : 0 ≤ a := Finset.le_inf' hs w (fun n _ => hw_nonneg n)
    have hb0 : 0 ≤ b := Finset.le_inf' hs u (fun n _ => hu0 n)
    have ha_le_w : ∀ n ∈ s, a ≤ w n := fun n hn => Finset.inf'_le w hn
    have ha_le_b : a ≤ b := by
      refine Finset.le_inf' hs u ?_
      intro n hn
      exact (ha_le_w n hn).trans inf_le_left
    have ha_le_pref : a ≤ inv • pref n0 := (ha_le_w n0 hn0_mem).trans inf_le_right
    have hb_disj_u_before : ∀ i ∈ Finset.range n0, IsVLDisjoint b (u i) := by
      intro i hi
      have hi_lt : i < n0 := by simpa using hi
      have hi_not : i ∉ s := by
        intro his
        exact (Nat.not_lt_of_ge (Finset.min'_le s i his)) hi_lt
      have hcard_insert : (insert i s).card = k + 1 := by
        simp [hi_not, hcard]
      have hne_insert : (insert i s : Finset ℕ).Nonempty :=
        ⟨i, Finset.mem_insert_self i s⟩
      have hinf := hu_disj (insert i s) hcard_insert hne_insert
      have hinf_eq : (insert i s).inf' hne_insert (fun j => |u j|) = u i ⊓ b := by
        rw [Finset.inf'_insert hs]
        rw [abs_of_nonneg (hu0 i)]
        congr 1
        apply Finset.inf'_congr hs rfl
        intro j _
        exact abs_of_nonneg (hu0 j)
      have hbi_zero : b ⊓ u i = 0 := by
        rw [hinf_eq] at hinf
        rwa [inf_comm] at hinf
      exact isVLDisjoint_of_inf_eq_zero hbi_zero
    have hb_disj_pref : IsVLDisjoint b (pref n0) := by
      simpa [pref] using isVLDisjoint_finset_sum hb_disj_u_before
    have hb_disj_invpref : IsVLDisjoint b (inv • pref n0) := hb_disj_pref.smul_right inv
    have ha_disj_invpref : IsVLDisjoint a (inv • pref n0) := by
      refine hb_disj_invpref.mono_left ?_
      rw [abs_of_nonneg ha0, abs_of_nonneg hb0]
      exact ha_le_b
    have ha_inf_zero : a ⊓ inv • pref n0 = 0 :=
      inf_eq_zero_of_isVLDisjoint ha0 (hinvpref0 n0) ha_disj_invpref
    have ha_eq_zero : a = 0 := by
      have : a ⊓ inv • pref n0 = a := inf_eq_left.mpr ha_le_pref
      exact this ▸ ha_inf_zero
    exact ha_eq_zero
  · have hdisj_gt : ∀ {n m : ℕ}, n < m → IsVLDisjoint (y m) (y n) := by
      intro n m hnm
      have hnm_succ : n + 1 ≤ m := Nat.succ_le_iff.mpr hnm
      have hpref_succ : pref (n + 1) = pref n + u n := by
        simp [pref, Finset.sum_range_succ]
      have hpref_nu_le_m : pref n + u n ≤ pref m := by
        rw [← hpref_succ]
        exact hpref_mono hnm_succ
      have hscale_y : eps • y m = (eps • u m - pref m - (eps * eps) • x)⁺ := by
        rw [← posPart_smul_nonneg heps_nonneg]
        congr 1
        rw [smul_sub, smul_sub, smul_smul, smul_smul]
        rw [show eps * inv = 1 by dsimp [inv]; exact mul_inv_cancel₀ heps_ne, one_smul]
      have harg_le₁ : eps • u m - pref m - (eps * eps) • x ≤
          eps • x - pref n - u n := by
        calc
          eps • u m - pref m - (eps * eps) • x ≤ eps • x - (pref n + u n) - 0 := by
            gcongr
            · exact hux m
            · exact smul_nonneg (mul_nonneg heps_nonneg heps_nonneg) hx0
          _ = eps • x - pref n - u n := by abel
      have hle₁ : eps • y m ≤ (eps • x - pref n - u n)⁺ := by
        rw [hscale_y]
        exact posPart_mono harg_le₁
      have hneg_pref_le : -pref n ≤ inv • pref n := by
        calc
          -pref n = (-1 : ℝ) • pref n := by simp
          _ ≤ inv • pref n := smul_le_smul_of_nonneg_right
            (by linarith : (-1 : ℝ) ≤ inv) (hpref0 n)
      have harg_le₂ : eps • x - pref n - u n ≤ inv • pref n + eps • x - u n := by
        calc
          eps • x - pref n - u n = eps • x + -pref n - u n := by abel
          _ ≤ eps • x + inv • pref n - u n := by
            gcongr
          _ = inv • pref n + eps • x - u n := by abel
      have hle₂ : eps • y m ≤ (inv • pref n + eps • x - u n)⁺ :=
        hle₁.trans (posPart_mono harg_le₂)
      have hneg_eq : (inv • pref n + eps • x - u n)⁺ =
          (u n - inv • pref n - eps • x)⁻ := by
        rw [negPart_def]
        congr 1
        abel
      have hbound : eps • y m ≤ (u n - inv • pref n - eps • x)⁻ := by
        rwa [hneg_eq] at hle₂
      have hbase : IsVLDisjoint (u n - inv • pref n - eps • x)⁻ (y n) := by
        exact isVLDisjoint_comm.mp (by
          simpa only [y] using isVLDisjoint_posPart_negPart
            (u n - inv • pref n - eps • x))
      have hscaled : IsVLDisjoint (eps • y m) (y n) := by
        refine hbase.mono_left ?_
        rw [abs_of_nonneg (smul_nonneg heps_nonneg (hy0 m)),
          abs_of_nonneg (negPart_nonneg (u n - inv • pref n - eps • x))]
        exact hbound
      have hres := hscaled.smul_left inv
      simpa [inv, smul_smul, heps_ne] using hres
    intro n m hnm
    rcases Nat.lt_or_gt_of_ne hnm with hlt | hgt
    · exact isVLDisjoint_comm.mp (hdisj_gt hlt)
    · exact hdisj_gt hgt
  · intro n
    constructor
    · exact le_inf (hu0 n) (hinvpref0 n)
    · exact inf_le_left.trans (hux n)
  · intro n
    constructor
    · exact hy0 n
    · have hy_le_u : y n ≤ u n := by
        refine sup_le ?_ (hu0 n)
        exact (sub_le_self _ hepsx0).trans (sub_le_self _ (hinvpref0 n))
      exact hy_le_u.trans (hux n)
  · intro n
    let p : E := inv • pref n
    let e : E := eps • x
    have hp0 : 0 ≤ p := hinvpref0 n
    have he0 : 0 ≤ e := hepsx0
    have hy_eq : y n = u n - u n ⊓ (p + e) := by
      rw [sub_inf_eq_posPart]
      simp [y, p, e]
      abel_nf
    have hdecomp : y n + u n ⊓ (p + e) = u n := by
      rw [hy_eq]
      abel
    constructor
    · calc
        y n + w n ≤ y n + u n ⊓ (p + e) := by
          gcongr
          exact inf_le_inf_left (u n) (le_add_of_nonneg_right he0)
        _ = u n := hdecomp
    · have hinf_le : u n ⊓ (p + e) ≤ w n + e := by
        calc
          u n ⊓ (p + e) ≤ u n ⊓ p + u n ⊓ e :=
            inf_le_inf_add_inf_of_nonneg (u n) p e (hu0 n) hp0 he0
          _ ≤ w n + e := by
            gcongr
            exact inf_le_right
      calc
        u n = y n + u n ⊓ (p + e) := hdecomp.symm
        _ ≤ y n + (w n + e) := by gcongr
        _ = y n + w n + eps • x := by simp [e]; abel
omit [IsOrderedAddMonoid E] [VectorLattice E] in
private lemma pairwise_of_isKDisjointSeq_two {u : ℕ → E}
    (hu : IsKDisjointSeq 2 u) :
    Pairwise fun n m => IsVLDisjoint (u n) (u m) := by
  intro n m hnm
  have hcard : ({n, m} : Finset ℕ).card = 2 := by simp [hnm]
  have hne : ({n, m} : Finset ℕ).Nonempty := ⟨n, by simp⟩
  have hinf := hu ({n, m} : Finset ℕ) hcard hne
  simpa [IsVLDisjoint, hnm, inf_comm] using hinf
private theorem split_isKDisjointSeq {x : E} :
    ∀ {k : ℕ} {u : ℕ → E}, 0 < k →
      (∀ n, u n ∈ Set.Icc (0 : E) x) → IsKDisjointSeq (k + 1) u →
      ∀ {eps : ℝ}, 0 < eps → eps < 1 →
      ∃ y : Fin k → ℕ → E,
        (∀ i, Pairwise fun n m => IsVLDisjoint (y i n) (y i m)) ∧
        (∀ i n, y i n ∈ Set.Icc (0 : E) x) ∧
        ∀ n, (∑ i : Fin k, y i n) ≤ u n ∧
          u n ≤ (∑ i : Fin k, y i n) + eps • x := by
  intro k
  induction k with
  | zero =>
      intro u hk
      exact (Nat.not_lt_zero _ hk).elim
  | succ k ih =>
      intro u hk hu_interval hu_disj eps heps0 heps1
      rcases k with _ | k
      · refine ⟨fun _ => u, ?_, ?_, ?_⟩
        · intro i
          exact pairwise_of_isKDisjointSeq_two hu_disj
        · intro i n
          exact hu_interval n
        · intro n
          have hx : 0 ≤ x := (hu_interval n).1.trans (hu_interval n).2
          have hepsx : 0 ≤ eps • x := smul_nonneg (le_of_lt heps0) hx
          simp [hepsx]
      · have heps_half_pos : 0 < eps / 2 := by
          positivity
        have heps_half_lt : eps / 2 < 1 := by linarith
        obtain ⟨w, y0, hw_disj, hy0_disj, hw_interval, hy0_interval, hwy⟩ :=
          disjointification_step_two hu_interval hu_disj heps_half_pos
        obtain ⟨yr, hyr_disj, hyr_interval, hyr_approx⟩ :=
          ih (by omega) hw_interval hw_disj heps_half_pos heps_half_lt
        let y : Fin (k.succ.succ) → ℕ → E := Fin.cons y0 yr
        refine ⟨y, ?_, ?_, ?_⟩
        · intro i
          induction i using Fin.cases with
          | zero =>
              exact hy0_disj
          | succ i =>
              exact hyr_disj i
        · intro i n
          induction i using Fin.cases with
          | zero =>
              exact hy0_interval n
          | succ i =>
              exact hyr_interval i n
        · intro n
          have hsum : (∑ i : Fin (k.succ.succ), y i n) = y0 n + ∑ i : Fin k.succ, yr i n := by
            simp [y, Fin.sum_univ_succ]
          constructor
          · rw [hsum]
            calc
              y0 n + ∑ i : Fin k.succ, yr i n ≤ y0 n + w n :=
                add_le_add_right (hyr_approx n).1 (y0 n)
              _ ≤ u n := (hwy n).1
          · have hupper := (hwy n).2
            have hrec := (hyr_approx n).2
            rw [hsum]
            have hscalar : (eps / 2) • x + (eps / 2) • x = eps • x := by
              rw [← add_smul]
              ring_nf
            calc
              u n ≤ y0 n + w n + (eps / 2) • x := hupper
              _ ≤ y0 n + ((∑ i : Fin k.succ, yr i n) + (eps / 2) • x) +
                    (eps / 2) • x := by
                    gcongr
              _ = y0 n + ∑ i : Fin k.succ, yr i n +
                    ((eps / 2) • x + (eps / 2) • x) := by abel
              _ = y0 n + ∑ i : Fin k.succ, yr i n + eps • x := by
                    rw [hscalar]
end Disjointification
section NormCriterion
variable {E : Type*} [NormedAddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [NormedVectorLattice E]
end NormCriterion
namespace BanachLattice
variable [BanachLattice X]
end BanachLattice
end
end

set_option autoImplicit true
@[expose] public section
public section
variable {X : Type*} [NormedAddCommGroup X] [Lattice X] [IsOrderedAddMonoid X]
variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [VectorLattice E]
theorem _root_.solution {x : E} {u : ℕ → E}
    (h0 : ∀ n, 0 ≤ u n) (hmono : Monotone u) (hle : ∀ n, u n ≤ x)
    {k : ℕ} (hk : 0 < k) :
    ∃ y : Fin k → ℕ → E,
      (∀ i, Pairwise fun n m => IsVLDisjoint (y i n) (y i m)) ∧
      (∀ i n, y i n ∈ Set.Icc (0 : E) x) ∧
      ∀ n, (∑ i : Fin k, y i n) ≤ u (n + 1) - u n ∧
        u (n + 1) - u n ≤
          (∑ i : Fin k, y i n) + ((2 : ℝ) / ((k : ℝ) + 3)) • x := by
  rcases k with _ | k
  · exact (Nat.not_lt_zero _ hk).elim
  rcases k with _ | k
  · obtain ⟨v, hv_disj, hv_interval, hv_approx⟩ :=
      disjointification_step_one h0 hmono hle 1
    refine ⟨fun _ => v, ?_, ?_, ?_⟩
    · intro i
      exact pairwise_of_isKDisjointSeq_two hv_disj
    · intro i n
      exact hv_interval n
    · intro n
      have hcoef :
          ((1 : ℝ) / ((1 : ℝ) + 1)) = ((2 : ℝ) / ((1 : ℝ) + 3)) := by
        norm_num
      simpa [hcoef] using hv_approx n
  · let K : ℕ := k.succ.succ
    obtain ⟨v, hv_disj, hv_interval, hv_approx⟩ :=
      disjointification_step_one h0 hmono hle K
    let eps : ℝ := (2 : ℝ) / ((K : ℝ) + 3) - (1 : ℝ) / ((K : ℝ) + 1)
    have heps0 : 0 < eps := by
      dsimp [eps]
      have hlt :
          (1 : ℝ) / ((K : ℝ) + 1) < (2 : ℝ) / ((K : ℝ) + 3) := by
        rw [div_lt_div_iff₀ (show 0 < (K : ℝ) + 1 by positivity)
          (show 0 < (K : ℝ) + 3 by positivity)]
        have hK : (1 : ℝ) < K := by exact_mod_cast (by omega : 1 < K)
        nlinarith
      linarith
    have heps1 : eps < 1 := by
      dsimp [eps]
      have hpos : 0 < (1 : ℝ) / ((K : ℝ) + 1) := by positivity
      have hlt : (2 : ℝ) / ((K : ℝ) + 3) < 1 := by
        rw [div_lt_one₀ (show 0 < (K : ℝ) + 3 by positivity)]
        have hKnonneg : (0 : ℝ) ≤ K := by positivity
        nlinarith
      linarith
    obtain ⟨y, hy_disj, hy_interval, hy_approx⟩ :=
      split_isKDisjointSeq (x := x) (k := K) (u := v) (by omega) hv_interval hv_disj
        heps0 heps1
    refine ⟨y, hy_disj, hy_interval, ?_⟩
    intro n
    constructor
    · exact (hy_approx n).1.trans (hv_approx n).1
    · calc
        u (n + 1) - u n ≤ v n + ((1 : ℝ) / ((K : ℝ) + 1)) • x := (hv_approx n).2
        _ ≤ ((∑ i : Fin K, y i n) + eps • x) +
              ((1 : ℝ) / ((K : ℝ) + 1)) • x :=
              add_le_add_left (hy_approx n).2 _
        _ = (∑ i : Fin K, y i n) + ((2 : ℝ) / ((K : ℝ) + 3)) • x := by
              have hscalar : eps • x + ((1 : ℝ) / ((K : ℝ) + 1)) • x =
                  ((2 : ℝ) / ((K : ℝ) + 3)) • x := by
                rw [← add_smul]
                congr 1
                simp [eps]
              calc
                (∑ i : Fin K, y i n) + eps • x +
                    ((1 : ℝ) / ((K : ℝ) + 1)) • x =
                    (∑ i : Fin K, y i n) +
                      (eps • x + ((1 : ℝ) / ((K : ℝ) + 1)) • x) := by abel
                _ = (∑ i : Fin K, y i n) + ((2 : ℝ) / ((K : ℝ) + 3)) • x := by
                    rw [hscalar]
