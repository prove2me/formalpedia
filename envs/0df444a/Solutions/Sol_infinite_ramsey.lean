-- Prove2me | solution 1 for infinite_ramsey
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:42:27.951171+00:00
-- url     : https://prove2.me/submissions/49c8f6a7-0fd1-4b1e-9d87-18d68d956061

module
public import Mathlib.Data.Finset.Card
public import Definitions.Def_LeanPool_NashWilliams_Data_Fintype_Pigeonhole
public import Definitions.Def_LeanPool_NashWilliams_Data_Nat_Nth
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Ramsey_Infinite
public import Theorems.Thm_exists_infinite_fiber_nat


set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
variable {κ : Type*}
theorem _root_.solution [Finite κ] (r : ℕ) (c : Finset ℕ → κ)
    {M : Set ℕ} (hM : M.Infinite) :
    ∃ N ⊆ M, N.Infinite ∧ ∃ col : κ,
      ∀ t : Finset ℕ, ↑t ⊆ N → t.card = r → c t = col := by
  induction r generalizing c M with
  | zero =>
    refine ⟨M, subset_rfl, hM, c ∅, fun t _ ht => ?_⟩
    rw [Finset.card_eq_zero.mp ht]
  | succ r ih =>
    have stepCore : ∀ S : Set ℕ, S.Infinite →
        ∃ a' ∈ S, ∃ (col' : κ) (N : Set ℕ),
          N.Infinite ∧ N ⊆ S ∧ (∀ x ∈ N, a' < x) ∧
          ∀ t : Finset ℕ, ↑t ⊆ N → t.card = r → c (insert a' t) = col' := by
      intro S hS
      refine ⟨sInf S, Nat.sInf_mem hS.nonempty, ?_⟩
      have hle : ∀ x ∈ S, sInf S ≤ x := fun x hx => Nat.sInf_le hx
      have hdiff : (S \ {sInf S}).Infinite := hS.sdiff (Set.finite_singleton _)
      obtain ⟨N, hNsub, hNinf, col', hmono⟩ := ih (fun e => c (insert (sInf S) e)) hdiff
      refine ⟨col', N, hNinf, hNsub.trans Set.sdiff_subset, ?_, hmono⟩
      intro x hxN
      have hxd := hNsub hxN
      exact lt_of_le_of_ne (hle x hxd.1) fun h => hxd.2 (h ▸ rfl)
    have advance : ∀ s : RamseyState c r, ∃ s' : RamseyState c r,
        s'.vert ∈ s.succ ∧ s'.succ ⊆ s.succ := by
      intro s
      obtain ⟨a', ha'mem, col', N, hNinf, hNsub, hNgt, hNprop⟩ := stepCore s.succ s.hInf
      exact ⟨⟨a', col', N, hNinf, hNgt, hNprop⟩, ha'mem, hNsub⟩
    obtain ⟨a₀, ha₀M, col₀, N₀, hN₀inf, hN₀sub, hN₀gt, hN₀prop⟩ := stepCore M hM
    let s₀ : RamseyState c r := ⟨a₀, col₀, N₀, hN₀inf, hN₀gt, hN₀prop⟩
    let states : ℕ → RamseyState c r := fun n => n.rec s₀ fun _ s => (advance s).choose
    have I1 : ∀ n, (states (n + 1)).vert ∈ (states n).succ :=
      fun n => (advance (states n)).choose_spec.1
    have I2 : ∀ n, (states (n + 1)).succ ⊆ (states n).succ :=
      fun n => (advance (states n)).choose_spec.2
    have I3 : ∀ n, (states n).vert < (states (n + 1)).vert :=
      fun n => (states n).hgt _ (I1 n)
    have I4 : ∀ m n, m ≤ n → (states n).succ ⊆ (states m).succ := by
      intro m n hmn
      induction n with
      | zero => simp [Nat.le_zero.mp hmn]
      | succ n ih2 =>
        rcases Nat.lt_or_eq_of_le hmn with h | rfl
        · exact (I2 n).trans (ih2 (Nat.lt_succ_iff.mp h))
        · exact subset_rfl
    have I5 : ∀ m n, m < n → (states n).vert ∈ (states m).succ := by
      intro m n hmn
      cases n with
      | zero => exact absurd hmn (Nat.not_lt_zero m)
      | succ n => exact I4 m n (Nat.lt_succ_iff.mp hmn) (I1 n)
    have vmono : StrictMono fun n => (states n).vert := strictMono_nat_of_lt_succ I3
    have hsuccM : ∀ n, (states n).succ ⊆ M := fun n => (I4 0 n (Nat.zero_le n)).trans hN₀sub
    have hvertM : ∀ n, (states n).vert ∈ M := by
      intro n
      cases n with
      | zero => exact ha₀M
      | succ n => exact hsuccM n (I1 n)
    obtain ⟨col, hJinf⟩ := exists_infinite_fiber_nat (fun n => (states n).col)
    set V : ℕ → ℕ := fun n => (states n).vert with hV
    set J : Set ℕ := {n | (states n).col = col} with hJ
    refine ⟨V '' J, ?_, hJinf.image (vmono.injective.injOn), col, ?_⟩
    · rintro x ⟨n, _, rfl⟩; exact hvertM n
    · intro t htN htcard
      have ht_ne : t.Nonempty := Finset.card_pos.mp (by rw [htcard]; exact Nat.succ_pos r)
      set a := t.min' ht_ne with ha
      have ha_mem : a ∈ t := Finset.min'_mem _ _
      obtain ⟨m, hmJ, hVm⟩ : ∃ m, (states m).col = col ∧ (states m).vert = a := by
        obtain ⟨m, hmJ, hVm⟩ := htN (Finset.mem_coe.mpr ha_mem)
        exact ⟨m, hmJ, hVm⟩
      have hsub : ↑(t.erase a) ⊆ (states m).succ := by
        intro x hx
        rw [Finset.mem_coe, Finset.mem_erase] at hx
        obtain ⟨hxne, hxt⟩ := hx
        obtain ⟨p, hpJ, hVp⟩ := htN (Finset.mem_coe.mpr hxt)
        have hax : a < x := lt_of_le_of_ne (Finset.min'_le t x hxt) (Ne.symm hxne)
        have hmp : m < p := by
          have h1 : (states m).vert < (states p).vert := by
            rw [hVm, show (states p).vert = x from hVp]; exact hax
          exact vmono.lt_iff_lt.mp h1
        have := I5 m p hmp
        rwa [show (states p).vert = x from hVp] at this
      have hcard : (t.erase a).card = r := by
        rw [Finset.card_erase_of_mem ha_mem, htcard]; omega
      have key := (states m).hprop (t.erase a) hsub hcard
      rw [hVm, Finset.insert_erase ha_mem, hmJ] at key
      exact key
