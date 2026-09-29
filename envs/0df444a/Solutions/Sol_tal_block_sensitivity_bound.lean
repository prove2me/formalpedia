-- Prove2me | solution 1 for tal_block_sensitivity_bound
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-05-08T21:28:08.382986+00:00
-- url     : https://prove2.me/submissions/4d2fc5e6-e62d-4cb5-99b7-9009b00cc4ef
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_polyDegree_distinguishing_units_bound
import Theorems.Thm_block_restrict_polyDegree_le
import Definitions.Def_BoolFunc
import Definitions.Def_blockSensitivity
import Definitions.Def_polyDegree
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic.Linarith

/-!
# Tal 2013 / Nisan–Szegedy block-sensitivity ⇔ degree bound

The quadratic bound `bs(f) ≤ 2 · deg(f)²` used by Huang 2019 to convert
the sensitivity/degree bound of Thm 1.4 into the sensitivity/block-
sensitivity bound of Thm 1.5.

Left as a platform leaf (`sorry`) — a full proof is outside the scope
of this decomposition pass.
-/


/-!
# Sketch — Tal/Nisan-Szegedy block-sensitivity bound

For Boolean `f : {0,1}ⁿ → {0,1}`, prove `bs(f) ≤ 2 · deg(f)²`.

Strategy:
1. Reduce, via `Finset.sup_le_iff`, to: for every `x` and every disjoint
   sensitive family `𝓑 ∈ sensitiveBlockFamilies f x`, `|𝓑| ≤ 2 · deg(f)²`.
2. Index `𝓑` by `Fin b` via `Finset.equivFin`. Build the block-restricted
   function `g : BoolFunc b` via `blockFlipMulti`.
3. Apply `block_restrict_polyDegree_le` (L2c) to get
   `polyDegree g ≤ polyDegree f`.
4. Compute `g(0) = f(x)` and `g(eᵢ) = f(flipBlock x (e i))`. Sensitivity
   gives `g(eᵢ) ≠ g(0)`.
5. Case-split on `f(x)`:
   - `f x = false`: `g` directly satisfies the L2 hypothesis.
   - `f x = true`: complement to `h y := !g y`; `polyDegree h ≤ polyDegree g`
     by inline `polyDegree_compl`; apply L2 to `h`.
6. Combine and unfold the suprema.
-/

open MvPolynomial

namespace TalBS

variable {n : ℕ}

/-- Inline lemma: complementing a Boolean function preserves its
    polyDegree (`1 - p` represents `!g` of the same total-degree). -/
lemma polyDegree_compl {b : ℕ} (g : BoolFunc b) :
    polyDegree (fun y => !g y) ≤ polyDegree g := by
  classical
  have hg : HasPolyRep g (polyDegree g) :=
    Nat.find_spec (⟨b, hasPolyRep_card g⟩ : ∃ d, HasPolyRep g d)
  obtain ⟨p, hp_deg, hp_eval⟩ := hg
  have h_compl : HasPolyRep (fun y => !g y) (polyDegree g) := by
    refine ⟨1 - p, ?_, ?_⟩
    · refine (totalDegree_sub _ _).trans ?_
      rw [totalDegree_one]
      exact Nat.max_le.mpr ⟨Nat.zero_le _, hp_deg⟩
    · intro y
      rw [map_sub, map_one, hp_eval y]
      cases h : g y
      · simp [h]
      · simp [h]
  show Nat.find _ ≤ _
  exact Nat.find_le h_compl

/-- The "weight-1 selector" `Function.update (fun _ => false) i true` flips
    exactly the block `e i` under `blockFlipMulti`. (No disjointness needed
    here; the basis vector activates only the `i`-th block by construction.) -/
lemma blockFlipMulti_basisVec {n b : ℕ} (x : Fin n → Bool)
    (e : Fin b → Finset (Fin n)) (i : Fin b) :
    blockFlipMulti x e (Function.update (fun _ => false) i true)
      = flipBlock x (e i) := by
  classical
  funext j
  unfold blockFlipMulti flipBlock
  by_cases hj : j ∈ e i
  · -- j ∈ e i
    have h_exists : ∃ k, j ∈ e k ∧ Function.update (fun _ => false) i true k = true := by
      refine ⟨i, hj, ?_⟩
      simp
    rw [if_pos h_exists, if_pos hj]
  · -- j ∉ e i
    rw [if_neg hj]
    rw [if_neg]
    rintro ⟨k, hjk, hyk⟩
    by_cases hki : k = i
    · subst hki; exact hj hjk
    · rw [Function.update_of_ne hki] at hyk
      exact Bool.false_ne_true hyk

/-- All-zero selector causes no flip. -/
lemma blockFlipMulti_zero {n b : ℕ} (x : Fin n → Bool)
    (e : Fin b → Finset (Fin n)) :
    blockFlipMulti x e (fun _ => false) = x := by
  classical
  funext j
  unfold blockFlipMulti
  rw [if_neg]
  rintro ⟨i, _, hyi⟩
  exact Bool.false_ne_true hyi

end TalBS

open TalBS

/-! ## Main proof. -/

theorem solution {n : ℕ} (f : BoolFunc n) :
    blockSensitivity f ≤ 2 * (polyDegree f) ^ 2 := by
  classical
  set d := polyDegree f with hd_def
  -- Unfold the outer sup
  unfold blockSensitivity
  rw [Finset.sup_le_iff]
  intros x _
  -- Unfold the inner sup over sensitive block families at x
  unfold blockSensitivityAt
  rw [Finset.sup_le_iff]
  intros 𝓑 h_𝓑
  -- Goal: 𝓑.card ≤ 2 * d^2
  -- 𝓑 ∈ sensitiveBlockFamilies f x: extract the witness and disjointness
  unfold sensitiveBlockFamilies at h_𝓑
  rw [Finset.mem_filter] at h_𝓑
  obtain ⟨_, h_sens, h_pwd⟩ := h_𝓑
  -- Trivial when 𝓑 is empty; main argument when |𝓑| ≥ 1
  by_cases hb : 1 ≤ 𝓑.card
  case neg =>
    have h0 : 𝓑.card = 0 := by omega
    rw [h0]; exact Nat.zero_le _
  -- Main case: 1 ≤ 𝓑.card
  -- Index 𝓑 by Fin (𝓑.card)
  set b := 𝓑.card with hb_def
  let e : Fin b → Finset (Fin n) := fun i => ((𝓑.equivFin.symm i) : Finset (Fin n))
  -- Each e i is in 𝓑
  have h_e_mem : ∀ i : Fin b, e i ∈ 𝓑 := fun i => (𝓑.equivFin.symm i).property
  -- The map e is injective
  have h_e_inj : Function.Injective e := by
    intros i j hij
    have h_subtype : 𝓑.equivFin.symm i = 𝓑.equivFin.symm j := Subtype.ext hij
    exact 𝓑.equivFin.symm.injective h_subtype
  -- Pairwise disjoint blocks via the family-level disjointness
  have h_disj : ∀ i j : Fin b, i ≠ j → Disjoint (e i) (e j) := by
    intros i j hij
    have h_ne : e i ≠ e j := fun heq => hij (h_e_inj heq)
    exact h_pwd (h_e_mem i) (h_e_mem j) h_ne
  -- Sensitivity at each block
  have h_e_sens : ∀ i : Fin b, IsSensitiveBlock f x (e i) :=
    fun i => h_sens (e i) (h_e_mem i)
  -- The block-restricted function on Fin b
  let g : BoolFunc b := fun y => f (blockFlipMulti x e y)
  -- L2c: polyDegree of restriction is bounded by polyDegree f
  have h_g_deg : polyDegree g ≤ d :=
    block_restrict_polyDegree_le f x e h_disj
  -- g(0) = f x
  have h_g_zero : g (fun _ => false) = f x := by
    show f (blockFlipMulti x e (fun _ => false)) = f x
    rw [blockFlipMulti_zero]
  -- g(eᵢ) = f (flipBlock x (e i))
  have h_g_unit_eq : ∀ i : Fin b,
      g (Function.update (fun _ => false) i true) = f (flipBlock x (e i)) := by
    intro i
    show f (blockFlipMulti x e _) = _
    rw [blockFlipMulti_basisVec x e i]
  -- g(eᵢ) ≠ g(0) by sensitivity
  have h_g_unit_ne : ∀ i : Fin b,
      g (Function.update (fun _ => false) i true) ≠ g (fun _ => false) := by
    intro i
    rw [h_g_unit_eq i, h_g_zero]
    exact (h_e_sens i).2
  -- Case-split on f x
  have h_b_le : b ≤ 2 * d ^ 2 := by
    cases hfx : f x
    · -- f x = false
      have h_g0 : g (fun _ => false) = false := by rw [h_g_zero]; exact hfx
      have h_g1 : ∀ i, g (Function.update (fun _ => false) i true) = true := by
        intro i
        have h_ne := h_g_unit_ne i
        rw [h_g0] at h_ne
        cases h : g (Function.update (fun _ => false) i true)
        · exact absurd h h_ne
        · rfl
      have h_L2 := polyDegree_distinguishing_units_bound hb g h_g0 h_g1
      calc b ≤ 2 * (polyDegree g) ^ 2 := h_L2
        _ ≤ 2 * d ^ 2 := by
            apply Nat.mul_le_mul_left
            exact Nat.pow_le_pow_left h_g_deg 2
    · -- f x = true; complement to (fun y => !g y)
      have h_g0 : g (fun _ => false) = true := by rw [h_g_zero]; exact hfx
      have h_h0 : (fun y : Fin b → Bool => !g y) (fun _ => false) = false := by
        simp [h_g0]
      have h_h1 : ∀ i, (fun y : Fin b → Bool => !g y)
                          (Function.update (fun _ => false) i true) = true := by
        intro i
        have h_ne := h_g_unit_ne i
        rw [h_g0] at h_ne
        cases hg : g (Function.update (fun _ => false) i true)
        · simp [hg]
        · exact absurd hg h_ne
      have h_h_deg : polyDegree (fun y : Fin b → Bool => !g y) ≤ polyDegree g :=
        polyDegree_compl g
      have h_L2 := polyDegree_distinguishing_units_bound hb
        (fun y : Fin b → Bool => !g y) h_h0 h_h1
      calc b ≤ 2 * (polyDegree (fun y : Fin b → Bool => !g y)) ^ 2 := h_L2
        _ ≤ 2 * (polyDegree g) ^ 2 := by
            apply Nat.mul_le_mul_left
            exact Nat.pow_le_pow_left h_h_deg 2
        _ ≤ 2 * d ^ 2 := by
            apply Nat.mul_le_mul_left
            exact Nat.pow_le_pow_left h_g_deg 2
  exact h_b_le
