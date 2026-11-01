-- Prove2me | Theorems.Thm_BaconThesis_Commutant_lemma_7_3_1
-- name    : BaconThesis.Commutant.lemma_7_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:38:26.978154+00:00
-- url     : https://prove2.me/theorems/11eff2c4-8c76-45b8-8f80-309ba2d47b77
-- title:
--   Lemma 7.3.1 — a Hamiltonian commuting with the OSR algebra acts only on the degeneracy of the $K$-th irrep
-- statement:
--   Let $A=\{W^\dagger(\bigoplus_J I_{n_J}\otimes X_J)W : X_J\in M_{d_J}\}\cong\bigoplus_{J\in\mathcal J}I_{n_J}\otimes M_{d_J}$ be an OSR (or SME) algebra in decomposed form, with $W$ unitary and $n_J,d_J\ge1$, let $K\in\mathcal J$ and let $P_K$ be the projector onto the subspace of the $K$-th irrep. Let $H$ be a Hamiltonian (a Hermitian operator) that commutes with every element of $A$. Then:
--   1. $H$ does not take information out of the $K$-th irrep:
--   $$
--   HP_K=P_KH ;
--   $$
--   2. on the $K$-th irrep, $H$ acts only on the degeneracy: there is a Hermitian $n_K\times n_K$ matrix $Y$ with
--   $$
--   HP_K=W^\dagger\bigl(0\oplus\cdots\oplus(Y\otimes I_{d_K})\oplus\cdots\oplus0\bigr)W ;
--   $$
--   3. for every time $t\in\mathbb R$ the evolution acts on the encoded information by $e^{-iYt}$ and keeps it in the degeneracy of the $K$-th irrep:
--   $$
--   e^{-iHt}P_K=W^\dagger\bigl(0\oplus\cdots\oplus(e^{-iYt}\otimes I_{d_K})\oplus\cdots\oplus0\bigr)W .
--   $$
--
--   This is the sufficient condition of §7.3 for a Hamiltonian to compute on information stored in a decoherence-free subsystem without leaking it out.
--
--   **Formalization Note** "Commutes with all of the elements of $A$" is membership in `Set.centralizer A`; $e^{-iHt}$ is the matrix exponential `NormedSpace.exp`.
--
--   Differences from the source:
--   - reading: "will act on this encoded information and will not take this encoded information out of the Kth irrep" → H P_K = P_K H, H P_K = W†(0 ⊕ (Y ⊗ I_{d_K}) ⊕ 0)W with Y Hermitian, and e^{−iHt} P_K = W†(0 ⊕ (e^{−iYt} ⊗ I_{d_K}) ⊕ 0)W for all real t; reason: the book's proof ("has the decomposition described in Eq. (7.2) which preserves the information encoded into the degeneracy") is exactly this block statement, and the three clauses express it for the operator and for its evolution
--   - encoding: A ≅ ⊕_J I_{n_J} ⊗ M_{d_J} → A = {W† (⊕_J I_{n_J} ⊗ X_J) W} for an explicit unitary W; reason: the basis change of Theorem 5.4.1 made explicit; same instances
--   - encoding: irreps J ∈ 𝒥 of Theorem 5.4.1 (each irrep present, with a degeneracy n_J and a dimension d_J) → hypotheses ∀ J, 0 < n J and ∀ J, 0 < d J; reason: the book's irreps and degeneracies are nonzero; an empty block would contribute nothing to any operator, so no instance changes
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §7.3, Lemma 7.3.1, p.100 (PDF p.117)

import Mathlib
import Definitions.Def_BaconThesis_Commutant_blockC
import Definitions.Def_BaconThesis_Commutant_algebraA
import Definitions.Def_BaconThesis_Commutant_irrepProj

namespace BaconThesis.Commutant

/-- **Lemma 7.3.1 (a Hamiltonian in the commutant acts only on the degeneracy of each irrep).**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§7.3, Lemma 7.3.1, p.100 (PDF p.117): "Suppose one is given an OSR or SME algebra
`A ≅ ⊕_{J∈𝒥} I_{n_J} ⊗ M_{d_J}` and information has been encoded into the degeneracy of the `K`th
irrep. A Hamiltonian `H` which commutes with all of the elements of `A` will act on this encoded
information and will not take this encoded information out of the `K`th irrep."

Let `A = {W† (⊕_J I_{n_J} ⊗ X_J) W}` as in `algebraA` (`W` unitary, `n_J, d_J ≥ 1`), let `K` be an
irrep label with projector `P_K` (`irrepProj`), and let `H` be a Hermitian operator commuting with
every element of `A`. Then
1. `H P_K = P_K H` (`H`, and hence `e^{−iHt}`, never moves a state out of the `K`-th irrep);
2. there is a Hermitian `n_K × n_K` matrix `Y` with `H P_K = W† (0 ⊕ ⋯ ⊕ (Y ⊗ I_{d_K}) ⊕ ⋯ ⊕ 0) W`
   (on the `K`-th irrep, `H` acts as `Y` on the degeneracy and as the identity on the irrep
   factor), and
3. for every time `t`, `e^{−iHt} P_K = W† (0 ⊕ ⋯ ⊕ (e^{−iYt} ⊗ I_{d_K}) ⊕ ⋯ ⊕ 0) W`: the evolution
   keeps the encoded information in the degeneracy of the `K`-th irrep and acts on it by `e^{−iYt}`.

**Formalization Note.** "Commutes with all of the elements of `A`" is `H ∈ Set.centralizer A`.
The single-block operators are `blockC` of `Pi.single K Y`. `e^{−iHt}` is
`NormedSpace.exp ((-(t : ℂ) * I) • H)`, for every real `t`. -/
theorem lemma_7_3_1 {𝒥 ι : Type} [Fintype 𝒥] [DecidableEq 𝒥] [Fintype ι] [DecidableEq ι]
    (n d : 𝒥 → ℕ) (hn : ∀ J, 0 < n J) (hd : ∀ J, 0 < d J)
    (W : Matrix (Σ J : 𝒥, Fin (n J) × Fin (d J)) ι ℂ)
    (hW₁ : W.conjTranspose * W = 1) (hW₂ : W * W.conjTranspose = 1)
    (K : 𝒥) (H : Matrix ι ι ℂ) (hH : H.IsHermitian) (hHA : H ∈ Set.centralizer (algebraA n d W)) :
    H * irrepProj n d W K = irrepProj n d W K * H ∧
      ∃ Y : Matrix (Fin (n K)) (Fin (n K)) ℂ, Y.IsHermitian ∧
        H * irrepProj n d W K =
          W.conjTranspose *
            blockC n d (Pi.single (M := fun J => Matrix (Fin (n J)) (Fin (n J)) ℂ) K Y) * W ∧
        ∀ t : ℝ, NormedSpace.exp ((-(t : ℂ) * Complex.I) • H) * irrepProj n d W K =
          W.conjTranspose *
            blockC n d (Pi.single (M := fun J => Matrix (Fin (n J)) (Fin (n J)) ℂ) K
              (NormedSpace.exp ((-(t : ℂ) * Complex.I) • Y))) * W := by sorry

end BaconThesis.Commutant
