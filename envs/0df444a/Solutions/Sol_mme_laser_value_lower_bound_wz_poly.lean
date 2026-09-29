-- Prove2me | solution 1 for mme_laser_value_lower_bound_wz_poly
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-01T15:56:02.6638+00:00
-- url     : https://prove2.me/submissions/5725ae75-b916-4905-9565-21ee409266f5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_laser_witness_at_prob_dist
import Definitions.Def_mme_laser_value_formula_wz
import Definitions.Def_mme_laser_pattern
import Definitions.Def_mme_subrank_capacity_poly

open MME BigOperators

universe u

/-! # Sketch: `mme_laser_value_lower_bound_wz_poly`

Decomposition of the abstract laser-method bound (real-formula +
polynomial-witness version) into a single Open intermediate Layer-5 leaf
plus a `sSup`-le-by-elements bridge.

## Reduction structure

```
mme_laser_value_lower_bound_wz_poly                ← this sketch
└── mme_laser_witness_at_prob_dist        (Open, new Layer-5)
         ↑ uses internally the 6 Layer-4 leaves:
         │  mme_3AP_free_no_collision
         │  mme_salem_spencer_eps_form
         │  mme_graded_tensor_pow_block_decomp
         │  mme_independent_blocks_form_direct_sum_restrict_enum
         │  mme_laser_block_dimension_count_refined
         │  mme_block_tensor_is_matMul_kronPow_balanced
```

The bridge from the *pointwise* bound (one π at a time) to the
*sup-over-distributions* bound is the standard `csSup_le` reduction over
the defining set of `laserValueFormula_wz`. The only subtlety is the
empty case (no valid probability distribution exists on `S` — happens
iff `S = ∅`), which is handled via `Real.sSup_empty`.

## Mathematical content

The intermediate leaf `mme_laser_witness_at_prob_dist` packages the full
analytic-combinatorial chain (steps 1–9 of the WZ §6 outline) at a fixed
`π`. The final step 10 (taking the sup over `π`) reduces to the abstract
`sSup` lemma and is performed here. -/

theorem solution {K : Type u} [Field K] {T : TensorObj K 3} {t : ℕ}
    (G : T.TypeGrading t) (S : Finset (Fin t × Fin t × Fin t))
    (hSym : LaserSymmetric S)
    (hsupport : TensorObj.LaserAlignedSupport G S) :
    laserValueFormula_wz G S ≤ subrankCapacityPoly T := by
  -- Unfold `laserValueFormula_wz` and reduce to a `sSup`-le statement.
  unfold laserValueFormula_wz
  -- The defining set of `laserValueFormula_wz`.
  set A : Set ℝ := { v : ℝ |
      ∃ π : (Fin t × Fin t × Fin t) → ℝ,
        (∀ σ, σ ∉ S → π σ = 0) ∧
        (∀ σ, 0 ≤ π σ) ∧
        (∑ σ ∈ S, π σ) = 1 ∧
        v = Real.exp (Real.log 2 *
          ( (-(∑ σ ∈ S, π σ * (Real.log (π σ) / Real.log 2)))
          + (1 / 3) *
              (∑ σ ∈ S, π σ *
                (Real.log
                    (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
                     ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
                     ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ))
                  / Real.log 2)) ) ) } with hA_def
  -- The pointwise bound from the new intermediate leaf.
  have hUB : ∀ v ∈ A, v ≤ subrankCapacityPoly T := by
    intro v hv
    rcases hv with ⟨π, hπ_supp, hπ_nn, hπ_sum, hv_eq⟩
    rw [hv_eq]
    exact mme_laser_witness_at_prob_dist G S hSym hsupport π hπ_supp hπ_nn hπ_sum
  -- Case-split: `A` empty (then `sSup ∅ = 0`) or nonempty (then `csSup_le`).
  by_cases hA_ne : A.Nonempty
  · -- Nonempty: classical `csSup_le`.
    exact csSup_le hA_ne hUB
  · -- Empty: `sSup ∅ = 0`. Show `0 ≤ subrankCapacityPoly T`.
    have hA_empty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA_ne
    rw [hA_empty, Real.sSup_empty]
    -- `subrankCapacityPoly T ≥ 0`: it is `sSup` of a set whose elements
    -- are all `≥ 1` (so the set is either empty — `sSup = 0` — or
    -- contains elements `≥ 1 ≥ 0` and `sSup ≥ 0` *if bounded*; for
    -- reals, `sSup_of_not_bddAbove = 0` covers the unbounded case).
    -- We handle all cases uniformly.
    set B : Set ℝ := { V : ℝ | 1 ≤ V ∧ ∃ c : ℝ,
      ∀ ε > (0 : ℝ), ∃ᶠ (N : ℕ) in Filter.atTop,
        ∃ (k : ℕ) (a b c' : Fin k → ℕ),
          (k : ℝ) ≤ ((N : ℝ) + 1) ^ c ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c' i)))
            (T.kronPow N)
          ∧ V ^ N * (1 - ε) ≤ ∑ i, ((a i * b i * c' i : ℕ) : ℝ) ^ ((1 : ℝ) / 3) }
        with hB_def
    have hBeq : subrankCapacityPoly T = sSup B := rfl
    rw [hBeq]
    by_cases hB_ne : B.Nonempty
    · -- B nonempty: pick V ∈ B; V ≥ 1 ≥ 0 ≤ sSup B (if bounded).
      -- If B is unbounded, sSup = 0 and we need 0 ≤ 0.
      by_cases hB_bdd : BddAbove B
      · obtain ⟨V₀, hV₀⟩ := hB_ne
        have hV₀_nn : (0 : ℝ) ≤ V₀ := le_trans zero_le_one hV₀.1
        exact le_trans hV₀_nn (le_csSup hB_bdd hV₀)
      · -- B unbounded: `sSup B = 0`.
        rw [Real.sSup_of_not_bddAbove hB_bdd]
    · -- B empty: `sSup B = 0`.
      rw [Set.not_nonempty_iff_eq_empty.mp hB_ne, Real.sSup_empty]
