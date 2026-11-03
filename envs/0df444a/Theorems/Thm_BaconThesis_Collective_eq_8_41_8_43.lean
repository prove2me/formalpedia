-- Prove2me | Theorems.Thm_BaconThesis_Collective_eq_8_41_8_43
-- name    : BaconThesis.Collective.eq_8_41_8_43
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:38.193138+00:00
-- url     : https://prove2.me/theorems/9ef908ce-4daa-4af2-85e7-eeafc8806a08
-- title:
--   Eqs. (8.41)–(8.43) — collective decoherence decomposition $\bigoplus_J I_{n_J}\otimes M_{2J+1}$ with $n_J=\frac{(2J+1)n!}{(n/2+J+1)!(n/2-J)!}$
-- statement:
--   Let $S_x,S_y,S_z$ be the collective operators $S_\alpha=\sum_{i=1}^n\tfrac12\sigma_\alpha^{(i)}$ on $n$ qubits, and let $\mathcal A$ be the complex algebra they generate together with the identity $I$. Let $J$ run over $n/2,\,n/2-1,\dots$, down to $0$ ($n$ even) or $\tfrac12$ ($n$ odd). Then there are multiplicities $n_J$ and a unitary
--   $$
--   W:\ \mathbb C^{2^n}\longrightarrow\bigoplus_J\mathbb C^{n_J}\otimes\mathbb C^{2J+1}
--   $$
--   such that
--   1. **(8.43)** for $\alpha=x,y,z$,
--   $$
--   W S_\alpha W^\dagger=\bigoplus_{J=0(1/2)}^{n/2} I_{n_J}\otimes S_\alpha(2J+1),
--   $$
--   where $S_\alpha(2J+1)$ is the standard $(2J+1)$-dimensional representation of $\mathfrak{su}(2)$;
--   2. **(8.42)** for every $J$,
--   $$
--   n_J=\frac{(2J+1)\,n!}{(n/2+J+1)!\,(n/2-J)!};
--   $$
--   3. **(8.41)** an operator $A$ on the $n$ qubits belongs to $\mathcal A$ if and only if
--   $$
--   W A W^\dagger=\bigoplus_J I_{n_J}\otimes X_J\quad\text{for some operators } X_J \text{ on } \mathbb C^{2J+1};
--   $$
--   that is, $W\mathcal A W^\dagger=\bigoplus_J I_{n_J}\otimes M_{2J+1}$, the whole algebra and not only a subalgebra of it.
--
--   This is the structure theorem of strong collective decoherence: information stored in the degeneracy factor $\mathbb C^{n_J}$ of a fixed $J$ is untouched by every error in $\mathcal A$, so each $J$ carries a decoherence-free subsystem $\mathrm{DFS}_n(J)$ of dimension $n_J$ (Definition 8.6.1).
--
--   **Formalization Note** $J=n/2-r$ with $r\in\{0,\dots,\lfloor n/2\rfloor\}$; the multiplicity formula is stated in $\mathbb Q$ with factorial arguments $n-r+1=n/2+J+1$ and $r=n/2-J$. The unitary is a matrix $W$ between the two index sets with $W^\dagger W=I$ and $WW^\dagger=I$.
--
--   Differences from the source:
--   - reading: A ≅ ⊕_J I_{n_J} ⊗ M_{2J+1} (8.41), "corresponding to the decomposition" S_α = ⊕_J I_{n_J} ⊗ S_α(2J+1) (8.43) → one unitary W such that W S_α W† is the block form (8.43) and W A W† ranges exactly over the block operators ⊕_J I ⊗ X_J for A in the algebra; reason: the isomorphism of (8.41) is the one implemented by the change of basis of (8.43), as the text says
--   - encoding: the 2J+1 dimensional representation of su(2) → the standard matrices spinRep (2J) (S_z diagonal, real nonnegative ladder coefficients); reason: all such irreps are unitarily equivalent and W absorbs the change of basis; the normalization is that of (8.50)
--   - encoding: J ∈ {n/2, n/2 − 1, …, 0 or 1/2}; n_J = (2J+1) n!/((n/2+J+1)!(n/2−J)!) → r ∈ Fin (⌊n/2⌋+1) with J = n/2 − r; (m r : ℚ) = (n−2r+1)·n!/((n−r+1)!·r!); reason: the same numbers without half-integers
--   - encoding: the decomposition of the Hilbert space → a matrix W indexed by BlockIdx n m × (Fin n → Fin 2) with W†W = I and WW† = I; reason: a unitary between two finite index sets
--   - generalization: n qubits, n ≥ 1 (the book starts at n = 1, (8.44)) → every n ∈ ℕ, including n = 0; reason: at n = 0 the space is one-dimensional and every collective operator is 0, where the statement also holds; for n ≥ 1 it is the book's statement
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, (8.41)–(8.43), §8.6, p.118 (PDF p.135)

import Mathlib
import Definitions.Def_BBPSSW_Distill_pauli
import Definitions.Def_BaconThesis_Collective_onQubit
import Definitions.Def_BaconThesis_Collective_collS
import Definitions.Def_BaconThesis_Collective_spinRep
import Definitions.Def_BaconThesis_Collective_BlockIdx
import Definitions.Def_BaconThesis_Collective_blockOp
import Definitions.Def_BaconThesis_Collective_degeneracy

open scoped Matrix

namespace BaconThesis.Collective

/-- **(8.41)–(8.43): the decomposition of `n` qubits under strong collective decoherence.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1, §8.6, (8.41)–(8.43), p.118 (PDF p.135): "The algebra `A` generated from `S_x^[n]`,
`S_y^[n]`, and `S_z^[n]` plus identity `I` can be decomposed as
`A ≅ ⊕_{J=0(1/2)}^{n/2} I_(n_J) ⊗ M_(2J+1)` (8.41) … The degeneracy of the `J`th irrep is given
by `n_J = (2J+1) n! / ((n/2 + J + 1)! (n/2 − J)!)` (8.42). Corresponding to the decomposition
Eq. (8.41) the action of the `S_α`'s act as `S_α = ⊕_{J=0(1/2)}^{n/2} I_(n_J) ⊗ S_α(2J+1)`
(8.43), where `S_α(2J+1)` is the `2J+1` dimensional representation of `su(2)`."

For every number of qubits `n` there are multiplicities `n_J` and a unitary
`W : ℂ^(2^n) → ⊕_J ℂ^(n_J) ⊗ ℂ^(2J+1)` (`J = n/2, n/2 − 1, …, 0 or 1/2`) such that

1. (8.43) `W S_α^[n] W† = ⊕_J I_(n_J) ⊗ S_α(2J+1)` for `α = x, y, z`;
2. (8.42) `n_J = (2J+1) n! / ((n/2 + J + 1)! (n/2 − J)!)` for every `J`;
3. (8.41) an operator `A` on the `n` qubits lies in the complex algebra generated by `I`, `S_x`,
   `S_y`, `S_z` if and only if `W A W† = ⊕_J I_(n_J) ⊗ X_J` for some operators `X_J` on
   `ℂ^(2J+1)`: the algebra is all of `⊕_J I_(n_J) ⊗ M_(2J+1)`.

**Formalization Note.** `J = n/2 − r` with `r ∈ Fin (⌊n/2⌋ + 1)`; the multiplicities are `m r`,
the irrep factor is `Fin (n − 2r + 1)` (`= 2J + 1`), and (8.42) is `degeneracy n r` (factorial
arguments `n − r + 1 = n/2 + J + 1`, `r = n/2 − J`). The unitary is a matrix `W` with
`W† W = I` and `W W† = I`. `Algebra.adjoin ℂ` contains the identity. The book takes `n ≥ 1`; the
statement is also true (and included) for `n = 0`. -/
theorem eq_8_41_8_43 (n : ℕ) :
    ∃ (m : Fin (n / 2 + 1) → ℕ) (W : Matrix (BlockIdx n m) (Fin n → Fin 2) ℂ),
      Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      (∀ α : BBPSSW.Distill.Axis, W * collS n α * Wᴴ = blockOp n m (fun r => spinRep (n - 2 * r.val) α)) ∧
      (∀ r : Fin (n / 2 + 1), (m r : ℚ) = degeneracy n r.val) ∧
      (∀ A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ,
        A ∈ Algebra.adjoin ℂ (Set.range (collS n)) ↔
          ∃ X : (r : Fin (n / 2 + 1)) →
              Matrix (Fin (n - 2 * r.val + 1)) (Fin (n - 2 * r.val + 1)) ℂ,
            W * A * Wᴴ = blockOp n m X) := by sorry

end BaconThesis.Collective
