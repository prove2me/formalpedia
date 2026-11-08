-- Prove2me | Theorems.Thm_BaconThesis_Multilevel_lemma_12_1_1
-- name    : BaconThesis.Multilevel.lemma_12_1_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T16:38:28.954496+00:00
-- url     : https://prove2.me/theorems/2fd46f8c-cac7-4718-af39-9764c837cd69
-- title:
--   Lemma 12.1.1: a non-degenerate multilevel atom with no isolated level has no DF subspace
-- statement:
--   Consider an $N$-level atom with levels $|1\rangle,\dots,|N\rangle$, real energies $\omega_1,\dots,\omega_N$, system Hamiltonian $H_0=\sum_i\omega_i|i\rangle\langle i|$, coupled to the electromagnetic field through coefficients $g_{ij}$ ($i>j$), and let $G$ be the symmetric transition matrix of (12.4). Assume
--
--   1. the energy spectrum is **non-degenerate**: $\omega_i\neq\omega_j$ for $i\neq j$;
--   2. **every level has a transition**: for every $i$ there is a $j$ with $G_{ij}\neq 0$.
--
--   Then the atom supports **no decoherence-free subspace** in the strict sense: there is no nonzero subspace $S\subseteq\mathbb C^N$ such that, for some constants $\alpha_1,\alpha_2$,
--
--   $$
--   \sum_{i>j} g_{ij}\sigma_{ij}|\psi\rangle=\alpha_1|\psi\rangle,\qquad \sum_{i>j} g^{*}_{ij}\sigma_{ij}|\psi\rangle=\alpha_2|\psi\rangle\qquad\text{for all }|\psi\rangle\in S,
--   $$
--
--   and $H_0$ preserves $S$ (Definition 5.3.2).
--
--   Hence a perfect DF subspace of a multilevel atom needs a degeneracy of its energy spectrum (or an isolated level). Both hypotheses are needed: an isolated level with non-degenerate energies, and a degenerate pair of levels coupled to each other, each carry a DF subspace.
--
--   **Formalization Note** Levels are indexed by `Fin N` (0-based), for every $N$; since $G_{ii}=0$, the level $j$ of hypothesis 2 differs from $i$. For $N\le 1$ hypothesis 2 cannot hold for $N=1$ and the statement is vacuous for $N=0$, as in the thesis.
--
--   Differences from the source:
--   - encoding: interaction with the quantized electromagnetic field (12.1)–(12.2) → the DF condition (12.3) on the two generators Σ g_ij σ_ij and Σ g*_ij σ_ij; reason: the thesis itself reduces the DF condition for this coupling to (12.3) through Theorem 5.3.1; the infinite-dimensional field lies outside the finite-dimensional framework of the thesis's Appendix A.3
--   - generalization: "DF subspace (in the strict sense of not evolving)" → (12.3) on S together with H₀ preserving S in the sense of Definition 5.3.2; reason: this is the notion the proof uses (§5.3.3); if "not evolving" is read as H₀ acting as a scalar on S, that implies preservation, so the Lean lemma excludes at least as many subspaces and specializes to that reading
--   - reading: Definition 5.3.2 "entirely outside of the subspace S" → orthogonal to every vector of S; reason: the reading "not in S" makes every Hamiltonian preserve every subspace, contradicting §5.3.3's purpose
--   - encoding: a DF subspace → a subspace S ≠ 0; reason: a subspace that supports a DF state is nonzero; the zero subspace satisfies every condition vacuously
--   - encoding: levels 1…N, energies ω_i, coefficients g_ij for i > j, non-degenerate spectrum → Fin N (0-based), ω : Fin N → ℝ injective, g : Fin N → Fin N → ℂ with entries for i ≤ j ignored; reason: Lean convention; same instances
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, Lemma 12.1.1, p.156 (PDF p.173)

import Mathlib
import Definitions.Def_BaconThesis_Multilevel_Gmat
import Definitions.Def_BaconThesis_Multilevel_IsDFSubspace

open scoped Matrix

namespace BaconThesis.Multilevel

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
Lemma 12.1.1, p.156 (PDF p.173): a multilevel system with a non-degenerate energy spectrum does
not support a DF subspace (in the strict sense of not evolving) with respect to interaction with
an electromagnetic field if every energy level has at least one non-vanishing transition to
another state (`G_ij ≠ 0` for every fixed `i` for at least one `j`).

**Formalization Note.** Levels are `Fin N` (0-based), any `N`; the energies `ω` are real and
non-degeneracy is injectivity of `ω`. The DF subspace is `IsDFSubspace`: the eigen-conditions
(12.3) on the two generators of the OSR algebra together with Definition 5.3.2 for
`H₀ = Σ_i ω_i |i⟩⟨i|`. The transition hypothesis is about the matrix `G` of (12.4); since
`G_ii = 0`, the `j` it provides differs from `i`. -/
theorem lemma_12_1_1 (N : ℕ) (ω : Fin N → ℝ) (hω : Function.Injective ω)
    (g : Fin N → Fin N → ℂ) (hG : ∀ i, ∃ j, Gmat g i j ≠ 0) :
    ¬ ∃ S : Submodule ℂ (Fin N → ℂ), IsDFSubspace g ω S := by sorry

end BaconThesis.Multilevel
