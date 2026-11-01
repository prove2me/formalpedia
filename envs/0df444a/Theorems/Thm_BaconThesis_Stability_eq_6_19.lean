-- Prove2me | Theorems.Thm_BaconThesis_Stability_eq_6_19
-- name    : BaconThesis.Stability.eq_6_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:59:17.367435+00:00
-- url     : https://prove2.me/theorems/82e2fcb0-ce57-4515-bfd6-966b47c00cc4
-- title:
--   Eq. (6.19) — $\Upsilon_J$ is cyclic under block operators
-- statement:
--   Let the system have the block basis $|K,\lambda,m\rangle$ ($K\in\mathcal J$, $\lambda\le n_K$, $m\le d_K$) and let $\Upsilon_J[X]=\sum_m\langle J,m|X|J,m\rangle$ be the subsystem trace onto the degeneracy of block $J$. For every family of $d_K\times d_K$ matrices $X_K$ and every operator $Y$ on the system,
--   $$
--   \Upsilon_J\Big[\Big(\bigoplus_K I_{n_K}\otimes X_K\Big)\,Y\Big]=\Upsilon_J\Big[Y\,\Big(\bigoplus_K I_{n_K}\otimes X_K\Big)\Big].
--   $$
--   In particular $\Upsilon_J[(I_{n_J}\otimes X_{d_J})Y]=\Upsilon_J[Y(I_{n_J}\otimes X_{d_J})]$.
--
--   This cyclicity of the partial trace over the factor on which block operators act is what makes every first-order contribution of a perturbation to the decoherence rates vanish.
--
--   Differences from the source:
--   - generalization: I_{n_J} ⊗ X_{d_J}, an operator on block J → blockOp n d X = ⊕_K I_{n_K} ⊗ X_K with X_J = X_{d_J} and the other blocks arbitrary; reason: taking X_K = 0 for K ≠ J (the operator on block J extended by zero) gives the book's statement
--   - encoding: finite-dimensional system and environment in a fixed basis (Appendix A.3) → index types with Fintype; system index Σ_K Fin n_K × Fin d_K (0-based), system-environment index S × E; reason: Lean convention; same instances
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §6.2, eq. (6.19), p.90 (PDF p.107)

import Mathlib
import Definitions.Def_BaconThesis_Stability_blockOp
import Definitions.Def_BaconThesis_Stability_upsilon

namespace BaconThesis.Stability

/-- **Eq. (6.19): `Υ_J` is cyclic under block operators.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§6.2, eq. (6.19), p.90 (PDF p.107): "`Υ_J[(I_{n_J} ⊗ X_{d_J}) Y] = Υ_J[Y (I_{n_J} ⊗ X_{d_J})]`".

For every family `X` of `d_K × d_K` matrices (one per block `K`) and every system operator `Y`,
`Υ_J[(⊕_K I_{n_K} ⊗ X_K) Y] = Υ_J[Y (⊕_K I_{n_K} ⊗ X_K)]`.

**Formalization Note.** The book's `I_{n_J} ⊗ X_{d_J}` is an operator on the `J`th block; on the full
system space it is written `blockOp n d X` with `X J = X_{d_J}` and the other blocks arbitrary (in
particular zero). The system index type is `Σ K : 𝒥, Fin (n K) × Fin (d K)`. -/
theorem eq_6_19 {𝒥 : Type} [Fintype 𝒥] [DecidableEq 𝒥] (n d : 𝒥 → ℕ) (J : 𝒥)
    (X : ∀ K, Matrix (Fin (d K)) (Fin (d K)) ℂ)
    (Y : Matrix (Σ K : 𝒥, Fin (n K) × Fin (d K)) (Σ K : 𝒥, Fin (n K) × Fin (d K)) ℂ) :
    upsilon n d J (blockOp n d X * Y) = upsilon n d J (Y * blockOp n d X) := by sorry

end BaconThesis.Stability
