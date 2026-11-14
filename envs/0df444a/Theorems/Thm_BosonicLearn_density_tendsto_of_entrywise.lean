-- Prove2me | Theorems.Thm_BosonicLearn_density_tendsto_of_entrywise
-- name    : BosonicLearn.density_tendsto_of_entrywise
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T09:44:02.762823+00:00
-- url     : https://prove2.me/theorems/dd724e09-b24a-435f-b17f-f2894e4dd238
-- title:
--   Entrywise convergence of density operators implies trace-norm convergence
-- statement:
--   For density operators, entrywise convergence in a fixed basis implies convergence in trace norm.
--
--   Let $I$ be an index set and let $X_0,X_1,X_2,\dots$ and $X$ be density operators on $\ell^2(I)$ (trace class, positive semidefinite, trace one), given by their coefficient arrays in the standard basis. If
--
--   $$
--   (X_k)_{ij}\longrightarrow X_{ij}\quad(k\to\infty)\qquad\text{for all } i,j\in I,
--   $$
--
--   then $\|X_k-X\|_1\to0$.
--
--   The hypothesis that the limit has trace one cannot be dropped: no mass escapes to infinity. Quantitatively, for a density operator $X$ and a finite $F\subseteq I$, the part of $X$ outside the block $F\times F$ has trace norm at most $2\sqrt{1-\sum_{i\in F}X_{ii}}$.
--
--   Role. For the hard family $\rho_{R_X}$ of the single-copy lower bound, the Fock-basis entries are polynomial in the fugacity matrix, hence continuous in $X$; this lemma upgrades that to the trace-norm continuity used in the proof of Theorem 5 ("which can be shown by appropriate photon number cutoff"). It applies equally to any family of states whose matrix elements depend continuously on parameters.
--
--   **Formalization Note** Density operators are `IsDensity` (trace class in the nuclear-expansion sense, non-negative quadratic forms on finitely supported vectors, diagonal sum $1$); $\|\cdot\|_1$ is `traceSize` with values in `ℝ≥0∞`; the conclusion is convergence to $0$ in `ℝ≥0∞` along `atTop`. The index set is arbitrary.
--
--   **Related platform material** The space $\ell^2(A)$ used here (`Hilbert A`) is the same Lean type as `OAI.TensorLp.H A`, and $\ell^2(\mathbb N^n)$ is the same type as `OAI.EntropyPhotonNumber.Fock n`. The published definitions `OAI_Analysis_TensorLp` (tensor products, slices and operator lifts on $\ell^2(A\times B)$) and `OAI_MathematicalPhysics_Fock_Operators` (`OAI.CrossEnsemble.operator`, the bounded operator $\sum_i|u_i\rangle\langle v_i|$ of a family, with `hasSum_operator` and `entry_hasSum`) are sorry-free and can be imported. Proved lemmas of this mission that can be imported: `BosonicLearn.traceDist_le_one` (nuclear expansions, truncation to finite index sets) and `BosonicLearn.effect_matrix_operator` (effect matrices as bounded positive operators).
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, proof of Theorem 5, p. 40 ("the map X ↦ ρ_{R_X} is continuous in trace norm (which can be shown by appropriate photon number cutoff)")

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity traceSize)
open Filter Topology
open scoped ENNReal

namespace BosonicLearn

/-- **Entrywise convergence of density operators implies convergence in trace norm.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, proof of Theorem 5, p. 40: "the map X ↦ ρ_{R_X} is continuous in trace norm (which can be shown by
appropriate photon number cutoff)".

Let `X₀, X₁, X₂, …` and `X` be density operators on `ℓ²(I)` (trace class, positive semidefinite, trace one), given
by their coefficient arrays. If `(X_k)_ij → X_ij` for all `i, j`, then `‖X_k − X‖₁ → 0`.

**Formalization Note.** `‖·‖₁` is `traceSize` with values in `ℝ≥0∞`. Because all operators have trace one, no
mass can escape: for a finite set `F` of basis indices the part of a density operator outside the block `F × F`
has trace norm at most `τ + 2√τ`, `τ = 1 − ∑_{i ∈ F} X_ii`, and `τ` converges along the sequence. -/
theorem density_tendsto_of_entrywise {I : Type} (X : ℕ → Matrix I I ℂ) (X₀ : Matrix I I ℂ)
    (hX : ∀ k, IsDensity (X k)) (hX₀ : IsDensity X₀)
    (h : ∀ i j, Tendsto (fun k => X k i j) atTop (𝓝 (X₀ i j))) :
    Tendsto (fun k => traceSize (X k - X₀)) atTop (𝓝 0) := by sorry

end BosonicLearn
