-- Prove2me | Theorems.Thm_BaconThesis_Commutant_lemma_7_4_1
-- name    : BaconThesis.Commutant.lemma_7_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:38:42.295944+00:00
-- url     : https://prove2.me/theorems/ad4780ff-424e-4d32-8c7b-d5ecc297357f
-- title:
--   Lemma 7.4.1 — measuring an observable in the commutant keeps encoded information in its irrep
-- statement:
--   Let $A=\{W^\dagger(\bigoplus_J I_{n_J}\otimes X_J)W : X_J\in M_{d_J}\}\cong\bigoplus_{J\in\mathcal J}I_{n_J}\otimes M_{d_J}$ be an OSR (or SME) algebra in decomposed form, with $W$ unitary and $n_J,d_J\ge1$. Let $M$ be a Hermitian observable in the commutant of $A$, let $K\in\mathcal J$ with irrep projector $P_K$, and let $\rho$ be a density operator carrying information encoded into the $K$-th irrep, i.e. $P_K\rho P_K=\rho$. Then for every real $\mu$, with $\Pi_\mu$ the projector onto the $\mu$-eigenspace of $M$, the post-measurement state for the outcome $\mu$ stays in the $K$-th irrep:
--   $$
--   P_K\,(\Pi_\mu\rho\,\Pi_\mu)\,P_K=\Pi_\mu\rho\,\Pi_\mu .
--   $$
--
--   So the commutant supplies measurements that read out encoded information without leaking it out of the decoherence-free subsystem.
--
--   **Formalization Note** The post-measurement state is written unnormalized; dividing by $\operatorname{tr}(\Pi_\mu\rho)$ does not change its support. Density operators are the platform's `WildeQIT.IsDensityOperator`.
--
--   Differences from the source:
--   - reading: "information … will remain in the irrep after a measurement of M" → for every outcome μ the projective post-measurement state Π_μ ρ Π_μ satisfies P_K (Π_μ ρ Π_μ) P_K = Π_μ ρ Π_μ, for every density operator ρ with P_K ρ P_K = ρ; reason: a measurement of a Hermitian observable is the projective measurement of its spectral decomposition, and "encoded into a irrep" means supported on that irrep's subspace
--   - encoding: A ≅ ⊕_J I_{n_J} ⊗ M_{d_J} → A = {W† (⊕_J I_{n_J} ⊗ X_J) W} for an explicit unitary W; reason: the basis change of Theorem 5.4.1 made explicit; same instances
--   - encoding: irreps J ∈ 𝒥 of Theorem 5.4.1 (each irrep present, with a degeneracy n_J and a dimension d_J) → hypotheses ∀ J, 0 < n J and ∀ J, 0 < d J; reason: the book's irreps and degeneracies are nonzero; an empty block would contribute nothing to any operator, so no instance changes
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §7.4, Lemma 7.4.1, p.104 (PDF p.121)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_BaconThesis_Commutant_algebraA
import Definitions.Def_BaconThesis_Commutant_irrepProj
import Definitions.Def_BaconThesis_Commutant_spectralProj

namespace BaconThesis.Commutant

/-- **Lemma 7.4.1 (measuring an observable in the commutant keeps information in its irrep).**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§7.4, Lemma 7.4.1, p.104 (PDF p.121): "Let `M` be a hermitian observable which is a member of the
commutant of the OSR or SME algebra `A`. Information which has been encoded into a irrep of the
algebra `A` will remain in the irrep after a measurement of `M`."

Let `A = {W† (⊕_J I_{n_J} ⊗ X_J) W}` as in `algebraA` (`W` unitary, `n_J, d_J ≥ 1`), let `M` be a
Hermitian operator commuting with every element of `A`, let `K` be an irrep label with projector
`P_K` (`irrepProj`), and let `ρ` be a density operator supported on the `K`-th irrep
(`P_K ρ P_K = ρ`). Then for every real `μ`, with `Π_μ` the projector onto the `μ`-eigenspace of `M`
(`spectralProj`), the (unnormalized) post-measurement state `Π_μ ρ Π_μ` for outcome `μ` is again
supported on the `K`-th irrep: `P_K (Π_μ ρ Π_μ) P_K = Π_μ ρ Π_μ`.

**Formalization Note.** A measurement of `M` is the projective measurement `{Π_μ}` of its spectral
decomposition; normalizing by `tr(Π_μ ρ)` does not change the support, and for `μ` not an
eigenvalue `Π_μ = 0`. Density operators are `WildeQIT.IsDensityOperator` (positive semidefinite,
trace one). -/
theorem lemma_7_4_1 {𝒥 ι : Type} [Fintype 𝒥] [DecidableEq 𝒥] [Fintype ι] [DecidableEq ι]
    (n d : 𝒥 → ℕ) (hn : ∀ J, 0 < n J) (hd : ∀ J, 0 < d J)
    (W : Matrix (Σ J : 𝒥, Fin (n J) × Fin (d J)) ι ℂ)
    (hW₁ : W.conjTranspose * W = 1) (hW₂ : W * W.conjTranspose = 1)
    (M : Matrix ι ι ℂ) (hM : M.IsHermitian) (hMA : M ∈ Set.centralizer (algebraA n d W))
    (K : 𝒥) (ρ : Matrix ι ι ℂ) (hρ : WildeQIT.IsDensityOperator ρ)
    (hρK : irrepProj n d W K * ρ * irrepProj n d W K = ρ) (μ : ℝ) :
    irrepProj n d W K * (spectralProj hM μ * ρ * spectralProj hM μ) * irrepProj n d W K =
      spectralProj hM μ * ρ * spectralProj hM μ := by sorry

end BaconThesis.Commutant
