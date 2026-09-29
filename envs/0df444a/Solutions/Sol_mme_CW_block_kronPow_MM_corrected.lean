-- Prove2me | solution 1 for mme_CW_block_kronPow_MM_corrected
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-06-05T03:30:24.877484+00:00
-- url     : https://prove2.me/submissions/63227e41-e2e8-4046-9675-20be25deb1f2

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Definitions.Def_mme_block_subtensor
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_CW_canonical_grading
import Definitions.Def_mme_CW_support_pattern
import Definitions.Def_mme_tensor_rank
import Theorems.Thm_mme_block_per_s_factorization
import Theorems.Thm_mme_CW_block_is_MM_at_002
import Theorems.Thm_mme_CW_block_is_MM_at_020
import Theorems.Thm_mme_CW_block_is_MM_at_200
import Theorems.Thm_mme_CW_block_is_MM_at_011
import Theorems.Thm_mme_CW_block_is_MM_at_101
import Theorems.Thm_mme_CW_block_is_MM_at_110

open MME BigOperators


/-! # CW kronPow MM Restrict — *corrected* replacement.

**Supersedes the FALSE** `mme_block_tensor_kronPow_balanced_dim_product`
(UUID `0a0eece9`) and the FALSE `mme_block_tensor_is_matMul_kronPow_balanced`
(UUID `48f74a41`). Both claimed `MMObj K (∏ finrank ...) ...` which is
mathematically incorrect for paper-agnostic blocks — see
`REPORT_block_MM_correction.md` + memory `feedback_block_is_MM_not_finrank.md`.

**The right shape.** Each `s ∈ CWSupportPattern` has its own `(a_s, b_s, c_s)`
read off from the CW support pattern (NOT from grading-class finranks):

| s | (a_s, b_s, c_s) |
|---|---|
| (0, 1, 1) | (1, 1, q) |
| (1, 0, 1) | (q, 1, 1) |
| (1, 1, 0) | (1, q, 1) |
| (0, 0, 2) | (1, 1, 1) |
| (0, 2, 0) | (1, 1, 1) |
| (2, 0, 0) | (1, 1, 1) |

For any type-sequence `τ : Fin N → CWSupportPattern`, `(CWObj K q).kronPow N`
Restricts from the multinomial-product MMObj whose three dimensions are
products over k of per-position `(a_{τ k}, b_{τ k}, c_{τ k})`.

**Proof** (when paper-agnostic factorization closes): direct application of
`mme_block_per_s_factorization` with the 6 PROVED CW per-s MM witnesses
(`mme_CW_block_is_MM_at_{002,020,200,011,101,110}`).
-/

/-- The (a_s, b_s, c_s) dimensions for each CW support element s — read off
from the laser pattern structure, NOT from grading-class finranks. -/
def cwBlockMMDim_sol (s : Fin 3 × Fin 3 × Fin 3) (q : ℕ) : ℕ × ℕ × ℕ :=
  if s = (0, 1, 1) then (1, 1, q)
  else if s = (1, 0, 1) then (q, 1, 1)
  else if s = (1, 1, 0) then (1, q, 1)
  else (1, 1, 1)


/-! # `Sol_mme_CW_block_kronPow_MM_corrected` — CW kronPow MM Restrict.

Thin wrapper around the paper-agnostic `mme_block_per_s_factorization`
instantiated with `cwCanonicalGrading q` + `CWSupportPattern` + the 6 PROVED
CW per-s MM witnesses. -/

open MME BigOperators

universe u

namespace MMECWBlockKronPowMMSol

variable {K : Type u} [Field K]

/-- The per-s MM-dim functions extracted from `cwBlockMMDim_sol`. -/
private def aOf (q : ℕ) (s : Fin 3 × Fin 3 × Fin 3) : ℕ := (cwBlockMMDim_sol s q).1
private def bOf (q : ℕ) (s : Fin 3 × Fin 3 × Fin 3) : ℕ := (cwBlockMMDim_sol s q).2.1
private def cOf (q : ℕ) (s : Fin 3 × Fin 3 × Fin 3) : ℕ := (cwBlockMMDim_sol s q).2.2

/-- Per-s MM witness: for each s ∈ CWSupportPattern, `MMObj K (aOf q s) (bOf q s) (cOf q s)`
Restricts to `(cwCanonicalGrading q).blockSubtensor s_fn`. Dispatches to the 6 PROVED
CW per-s witness theorems via case-analysis on the 6 elements of CWSupportPattern. -/
private lemma per_s_MM_witness (q : ℕ) (s : Fin 3 × Fin 3 × Fin 3)
    (hs : s ∈ CWSupportPattern) :
    TensorObj.Restrict (MMObj K (aOf q s) (bOf q s) (cOf q s))
      ((cwCanonicalGrading q (K := K)).blockSubtensor (fun i : Fin 3 =>
        match i with
        | ⟨0, _⟩ => s.1
        | ⟨1, _⟩ => s.2.1
        | ⟨2, _⟩ => s.2.2)) := by
  -- CWSupportPattern = {(0,1,1), (1,0,1), (1,1,0), (0,0,2), (0,2,0), (2,0,0)}
  -- For each, dispatch to the corresponding witness with the matching cwBlockMMDim.
  unfold CWSupportPattern at hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with h | h | h | h | h | h
  · -- s = (0, 1, 1) → MMObj K 1 1 q
    subst h
    show TensorObj.Restrict (MMObj K (aOf q (0, 1, 1)) (bOf q (0, 1, 1))
        (cOf q (0, 1, 1))) _
    -- aOf, bOf, cOf at (0,1,1) = (1, 1, q)
    show TensorObj.Restrict (MMObj K 1 1 q) _
    exact mme_CW_block_is_MM_at_011 (K := K) q
  · -- s = (1, 0, 1) → MMObj K q 1 1
    subst h
    show TensorObj.Restrict (MMObj K q 1 1) _
    exact mme_CW_block_is_MM_at_101 (K := K) q
  · -- s = (1, 1, 0) → MMObj K 1 q 1
    subst h
    show TensorObj.Restrict (MMObj K 1 q 1) _
    exact mme_CW_block_is_MM_at_110 (K := K) q
  · -- s = (0, 0, 2) → MMObj K 1 1 1
    subst h
    show TensorObj.Restrict (MMObj K 1 1 1) _
    exact mme_CW_block_is_MM_at_002 (K := K) q
  · -- s = (0, 2, 0) → MMObj K 1 1 1
    subst h
    show TensorObj.Restrict (MMObj K 1 1 1) _
    exact mme_CW_block_is_MM_at_020 (K := K) q
  · -- s = (2, 0, 0) → MMObj K 1 1 1
    subst h
    show TensorObj.Restrict (MMObj K 1 1 1) _
    exact mme_CW_block_is_MM_at_200 (K := K) q

end MMECWBlockKronPowMMSol

open MMECWBlockKronPowMMSol

/-- CW corollary: directly applies paper-agnostic per-s factorization with the
6 PROVED CW per-s MM witnesses. -/
theorem solution {K : Type u} [Field K] (q : ℕ) (N : ℕ)
    (τ : Fin N → Fin 3 × Fin 3 × Fin 3)
    (hτ_in_S : ∀ k : Fin N, τ k ∈ CWSupportPattern) :
    TensorObj.Restrict
      (MMObj K
        (∏ k : Fin N, (cwBlockMMDim_sol (τ k) q).1)
        (∏ k : Fin N, (cwBlockMMDim_sol (τ k) q).2.1)
        (∏ k : Fin N, (cwBlockMMDim_sol (τ k) q).2.2))
      ((CWObj K q).kronPow N) := by
  -- The product over τ matches aOf/bOf/cOf via cwBlockMMDim_sol projections.
  show TensorObj.Restrict
    (MMObj K
      (∏ k : Fin N, aOf q (τ k))
      (∏ k : Fin N, bOf q (τ k))
      (∏ k : Fin N, cOf q (τ k)))
    ((CWObj K q).kronPow N)
  exact mme_block_per_s_factorization
    (cwCanonicalGrading q (K := K))
    CWSupportPattern
    (aOf q) (bOf q) (cOf q)
    (per_s_MM_witness (K := K) q)
    N τ hτ_in_S
