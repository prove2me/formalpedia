-- Prove2me | solution 1 for iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/fe0191bc-5093-584a-9afd-fd5955d5963f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex

set_option autoImplicit false

open Set Fin Function

namespace SymmWithin

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def liftPerm {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, e)

@[scoped simp] theorem liftPerm_zero {n : ℕ} (e : Equiv.Perm (Fin n)) : liftPerm e 0 = 0 := by
  simp [liftPerm]

@[scoped simp] theorem liftPerm_succ {n : ℕ} (e : Equiv.Perm (Fin n)) (k : Fin n) :
    liftPerm e k.succ = (e k).succ := by
  simp [liftPerm]

theorem decomposeFin_symm_eq {n : ℕ} (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    Equiv.Perm.decomposeFin.symm (p, e) = Equiv.swap 0 p * liftPerm e := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [liftPerm]
  · rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.Perm.coe_mul, comp_apply, liftPerm_succ]

theorem swap_one_succ_succ_eq_liftPerm {n : ℕ} (q : Fin (n + 1)) :
    (Equiv.swap (1 : Fin (n + 2)) q.succ) = liftPerm (Equiv.swap 0 q) := by
  refine Equiv.ext fun i => ?_
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [liftPerm_zero, Equiv.swap_apply_of_ne_of_ne (by simp) (Fin.succ_ne_zero q).symm]
  · rw [liftPerm_succ, ← Fin.succ_zero_eq_one]
    by_cases h0 : k = 0
    · subst h0; simp
    · by_cases hq : k = q
      · subst hq; simp
      · rw [Equiv.swap_apply_of_ne_of_ne ((Fin.succ_injective _).ne h0) ((Fin.succ_injective _).ne hq),
          Equiv.swap_apply_of_ne_of_ne h0 hq]

def P (s : Set E) (n : ℕ) : Prop :=
  ∀ (f : E → F), ContDiffOn ℝ n f s → ∀ x ∈ s, ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E),
    iteratedFDerivWithin ℝ n f s x (v ∘ σ) = iteratedFDerivWithin ℝ n f s x v

theorem P_of_subsingleton {s : Set E} {n : ℕ} (h : Subsingleton (Equiv.Perm (Fin n))) : P (F := F) s n := by
  intro f hf x hx σ v
  rw [Subsingleton.elim σ 1, Equiv.Perm.coe_one, comp_id]

theorem P_step {s : Set E} (hs : Convex ℝ s) (hs' : (interior s).Nonempty) (n : ℕ)
    (ih : P (F := F) s (n + 1)) : P (F := F) s (n + 2) := by
  have hU : UniqueDiffOn ℝ s := uniqueDiffOn_convex hs hs'
  intro f hf x hx

  have hmul : ∀ σ τ : Equiv.Perm (Fin (n + 2)),
      (∀ v : Fin (n + 2) → E, iteratedFDerivWithin ℝ (n + 2) f s x (v ∘ σ) = iteratedFDerivWithin ℝ (n + 2) f s x v) →
      (∀ v : Fin (n + 2) → E, iteratedFDerivWithin ℝ (n + 2) f s x (v ∘ τ) = iteratedFDerivWithin ℝ (n + 2) f s x v) →
      ∀ v : Fin (n + 2) → E, iteratedFDerivWithin ℝ (n + 2) f s x (v ∘ ⇑(σ * τ)) =
        iteratedFDerivWithin ℝ (n + 2) f s x v := by
    intro σ τ hσ hτ v
    rw [Equiv.Perm.coe_mul, ← comp_assoc, hτ (v ∘ σ), hσ v]

  have hlift : ∀ (e : Equiv.Perm (Fin (n + 1))) (v : Fin (n + 2) → E),
      iteratedFDerivWithin ℝ (n + 2) f s x (v ∘ liftPerm e) = iteratedFDerivWithin ℝ (n + 2) f s x v := by
    intro e v
    have hf' : ContDiffOn ℝ (n + 1 : ℕ) f s := hf.of_le (by exact_mod_cast Nat.le_succ _)
    let L := (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E F e).toContinuousLinearEquiv
    have hL : ∀ (M : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => E) F) (w : Fin (n + 1) → E),
        L M w = M (w ∘ e) := fun M w => rfl
    have heq : EqOn (L ∘ iteratedFDerivWithin ℝ (n + 1) f s) (iteratedFDerivWithin ℝ (n + 1) f s) s := by
      intro y hy
      ext w
      show L (iteratedFDerivWithin ℝ (n + 1) f s y) w = _
      rw [hL]
      exact ih f hf' y hy e w
    rw [iteratedFDerivWithin_succ_apply_left, iteratedFDerivWithin_succ_apply_left]
    have h0 : (v ∘ liftPerm e) 0 = v 0 := by simp
    have ht : tail (v ∘ liftPerm e) = tail v ∘ e := by
      funext k; simp [tail]
    rw [h0, ht, ← hL]
    calc L (fderivWithin ℝ (iteratedFDerivWithin ℝ (n + 1) f s) s x (v 0)) (tail v)
        = (fderivWithin ℝ (⇑L ∘ iteratedFDerivWithin ℝ (n + 1) f s) s x (v 0)) (tail v) := by
          rw [L.comp_fderivWithin (hU x hx)]; rfl
      _ = (fderivWithin ℝ (iteratedFDerivWithin ℝ (n + 1) f s) s x (v 0)) (tail v) := by
          rw [fderivWithin_congr' heq hx]

  have hswap01 : ∀ v : Fin (n + 2) → E,
      iteratedFDerivWithin ℝ (n + 2) f s x (v ∘ Equiv.swap 0 1) = iteratedFDerivWithin ℝ (n + 2) f s x v := by
    intro v
    set g := iteratedFDerivWithin ℝ n f s with hg
    have hg2 : ContDiffWithinAt ℝ 2 g s x :=
      (hf x hx).iteratedFDerivWithin_right hU (by exact_mod_cast (by omega : 2 + n ≤ n + 2)) hx
    have hsymm : IsSymmSndFDerivWithinAt ℝ g s x := by
      refine hg2.isSymmSndFDerivWithinAt (by simp) hU ?_ hx
      rw [hs.closure_interior_eq_closure_of_nonempty_interior hs']
      exact subset_closure hx
    have key : ∀ m : Fin (n + 2) → E, iteratedFDerivWithin ℝ (n + 2) f s x m =
        (fderivWithin ℝ (fderivWithin ℝ g s) s x (m 0) (m 1)) (tail (tail m)) := by
      intro m
      rw [iteratedFDerivWithin_succ_apply_left]
      have h1 : iteratedFDerivWithin ℝ (n + 1) f s =
          (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).symm.toContinuousLinearEquiv ∘
            fderivWithin ℝ g s := iteratedFDerivWithin_succ_eq_comp_left
      have h2 := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F).symm.toContinuousLinearEquiv
        |>.comp_fderivWithin (hU x hx) (f := fderivWithin ℝ g s)
      rw [h1, h2]
      rfl
    rw [key, key, hsymm.eq]
    congr 1

  have hswap0 : ∀ (p : Fin (n + 2)) (v : Fin (n + 2) → E),
      iteratedFDerivWithin ℝ (n + 2) f s x (v ∘ Equiv.swap 0 p) = iteratedFDerivWithin ℝ (n + 2) f s x v := by
    intro p
    refine Fin.cases ?_ (fun q => ?_) p
    · intro v; rw [Equiv.swap_self]; rfl
    · refine Fin.cases ?_ (fun r => ?_) q
      · exact hswap01
      ·
        have hne01 : (0 : Fin (n + 2)) ≠ 1 := by simp
        have hne0p : (0 : Fin (n + 2)) ≠ r.succ.succ := (Fin.succ_ne_zero _).symm
        have hdec : Equiv.swap (0 : Fin (n + 2)) r.succ.succ =
            Equiv.swap 1 r.succ.succ * Equiv.swap 0 1 * Equiv.swap 1 r.succ.succ := by
          rw [Equiv.swap_mul_swap_mul_swap hne01 hne0p, Equiv.swap_comm]
        have h1p : ∀ v : Fin (n + 2) → E,
            iteratedFDerivWithin ℝ (n + 2) f s x (v ∘ Equiv.swap 1 r.succ.succ) =
              iteratedFDerivWithin ℝ (n + 2) f s x v := by
          intro v
          rw [swap_one_succ_succ_eq_liftPerm]
          exact hlift _ v
        rw [hdec]
        exact hmul _ _ (hmul _ _ h1p hswap01) h1p

  intro σ v
  obtain ⟨⟨p, e⟩, rfl⟩ := Equiv.Perm.decomposeFin.symm.surjective σ
  rw [decomposeFin_symm_eq]
  exact hmul _ _ (hswap0 p) (hlift e) v

theorem P_all {s : Set E} (hs : Convex ℝ s) (hs' : (interior s).Nonempty) : ∀ n, P (F := F) s n := by
  intro n
  induction n with
  | zero => exact P_of_subsingleton ⟨fun a b => Equiv.ext fun i => i.elim0⟩
  | succ n ih =>
    cases n with
    | zero => exact P_of_subsingleton ⟨fun a b => Equiv.ext fun i => Subsingleton.elim (α := Fin 1) _ _⟩
    | succ k => exact P_step hs hs' k ih

end SymmWithin
p2m_reactivate "P2MW.S_iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex.SymmWithin"

theorem solution
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set E} (hs : Convex ℝ s) (hs' : (interior s).Nonempty)
    {n : ℕ} {f : E → F} (hf : ContDiffOn ℝ n f s) {x : E} (hx : x ∈ s)
    (σ : Equiv.Perm (Fin n)) (v : Fin n → E) :
    iteratedFDerivWithin ℝ n f s x (v ∘ σ) = iteratedFDerivWithin ℝ n f s x v :=
  SymmWithin.P_all hs hs' n f hf x hx σ v

end S_iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex
end P2MW
export P2MW.S_iteratedFDerivWithin_comp_equivPerm_of_contDiffOn_of_convex (solution)
