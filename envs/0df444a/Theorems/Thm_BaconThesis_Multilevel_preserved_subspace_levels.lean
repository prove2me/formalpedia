-- Prove2me | Theorems.Thm_BaconThesis_Multilevel_preserved_subspace_levels
-- name    : BaconThesis.Multilevel.preserved_subspace_levels
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:37:18.763868+00:00
-- url     : https://prove2.me/theorems/5a69968b-59ec-4ab9-a070-5140987ec503
-- title:
--   Lemma 12.1.1, proof: a subspace preserved by a non-degenerate $H_0$ is spanned by the levels it contains
-- statement:
--   Let $\omega_1,\dots,\omega_N$ be pairwise distinct real energies (a **non-degenerate** spectrum) and $H_0=\sum_i \omega_i|i\rangle\langle i|$. If $H_0$ preserves a subspace $S\subseteq\mathbb C^N$ in the sense of Definition 5.3.2, then
--
--   $$
--   S = \operatorname{span}\{\,|i\rangle \;:\; |i\rangle\in S\,\}.
--   $$
--
--   In the proof of Lemma 12.1.1 this is the step "the diagonalized form of $H_0$ is unique because the spectrum is non-degenerate, so the level $|i\rangle$ must be a state of the DF subspace in order that $H_0$ preserve it": a preserved nonzero subspace contains a level, and every level on which one of its states has a nonzero amplitude.
--
--   **Formalization Note** Levels are indexed by `Fin N` (0-based); $|i\rangle$ is the standard basis vector; non-degeneracy is injectivity of $\omega$.
--
--   Differences from the source:
--   - reading: "the state |i⟩ must be a DF state for the supposed DF subspace" → S is the span of the levels |i⟩ that lie in S; reason: the proof applies the sentence to the levels on which a DF state is supported; the span form states this for every such level and gives a level in S whenever S ≠ 0
--   - reading: Definition 5.3.2 "entirely outside of the subspace S" → orthogonal to every vector of S; reason: the reading "not in S" makes every Hamiltonian preserve every subspace, contradicting §5.3.3's purpose
--   - encoding: H₀ = Σ_i ω_i|i⟩⟨i| with a non-degenerate spectrum → Matrix.diagonal of real ω with ω injective, levels Fin N (0-based); reason: Lean convention; same instances
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, proof of Lemma 12.1.1, p.156 (PDF p.173), with Definition 5.3.2, §5.3.3, p.74 (PDF p.91)

import Mathlib
import Definitions.Def_BaconThesis_Multilevel_PreservesSubspace

open scoped Matrix

namespace BaconThesis.Multilevel

/-- Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
proof of Lemma 12.1.1, p.156 (PDF p.173), with Definition 5.3.2, p.74 (PDF p.91): if the energy
spectrum `ω` is non-degenerate, the diagonal form `H₀ = Σ_i ω_i |i⟩⟨i|` is unique, so a subspace
`S` preserved by `H₀` is spanned by the levels `|i⟩` that lie in `S`.

**Formalization Note.** Levels are `Fin N` (0-based); `|i⟩` is `Pi.single i 1`; `H₀` is
`Matrix.diagonal (fun i => ω i)` with real `ω`; non-degeneracy is injectivity of `ω`.
"Preserves" is Definition 5.3.2 (`PreservesSubspace`). -/
theorem preserved_subspace_levels {N : ℕ} (ω : Fin N → ℝ) (hω : Function.Injective ω)
    (S : Submodule ℂ (Fin N → ℂ))
    (hS : PreservesSubspace (Matrix.diagonal fun i => ((ω i : ℝ) : ℂ)) S) :
    S = Submodule.span ℂ ((fun i => (Pi.single i (1 : ℂ) : Fin N → ℂ)) ''
      {i | (Pi.single i (1 : ℂ) : Fin N → ℂ) ∈ S}) := by sorry

end BaconThesis.Multilevel
