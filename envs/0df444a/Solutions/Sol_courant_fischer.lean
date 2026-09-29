-- Prove2me | solution 1 for courant_fischer
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-05-03T01:06:02.353477+00:00
-- url     : https://prove2.me/submissions/611d6e46-3fed-4218-815f-4211e8ffba4a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_hermitian_kth_eigenvalue_witness
import Theorems.Thm_hermitian_kth_eigenvalue_dual_witness
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Star

open Matrix

/-!
# Courant–Fischer min-max characterization (descending, witness form)

For any Hermitian real matrix `A : Matrix V V ℝ` and descending-sorted index
`k`, the `k`-th eigenvalue admits a min-max characterization in terms of
Rayleigh quotients on subspaces:

   `λ_k = min over (n − k)-dim subspaces W of (max Rayleigh on W).`

We package the two halves of this min-max equality in *constructive existence
form*:

* **`≥` half**: every `(n − k)`-dim subspace `W` contains a vector `v ≠ 0`
  with `λ_k ≤ Rayleigh(v)` (so the max-Rayleigh on `W` is at least `λ_k`).
* **`≤` half**: there exists an `(n − k)`-dim subspace `W` on which
  `Rayleigh(u) ≤ λ_k` for every `u ∈ W` (the max-Rayleigh on this `W` is
  at most `λ_k`).

Together these give the min-max equality. Applying the theorem to `−A`
recovers the dual *max-min* characterization
`λ_k = max over (k+1)-dim subspaces of min Rayleigh`. So this single
statement encapsulates the full Courant–Fischer theorem for sorted real
Hermitian eigenvalues.

This is a foundational spectral-theory result underlying Cauchy interlacing,
Weyl's inequalities, and most monotonicity-style arguments on sorted
eigenvalues. **Not currently in Mathlib in this form.**
-/


open Matrix

/-!
# Sketch — `courant_fischer` is the conjunction of the two witness primitives

The `≥` half is exactly `hermitian_kth_eigenvalue_witness`; the `≤` half is
exactly `hermitian_kth_eigenvalue_dual_witness`. Pair them.
-/

theorem solution
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {A : Matrix V V ℝ} (hA : A.IsHermitian) (k : Fin (Fintype.card V)) :
    (∀ W : Submodule ℝ (V → ℝ),
        Fintype.card V - (k : ℕ) ≤ Module.finrank ℝ W →
        ∃ v ∈ W, v ≠ 0 ∧ hA.eigenvalues₀ k * (v ⬝ᵥ v) ≤ A *ᵥ v ⬝ᵥ v) ∧
    (∃ W : Submodule ℝ (V → ℝ),
        Module.finrank ℝ W = Fintype.card V - (k : ℕ) ∧
        ∀ u ∈ W, A *ᵥ u ⬝ᵥ u ≤ hA.eigenvalues₀ k * (u ⬝ᵥ u)) :=
  ⟨fun _W hW => hermitian_kth_eigenvalue_witness hA k hW,
   hermitian_kth_eigenvalue_dual_witness hA k⟩
