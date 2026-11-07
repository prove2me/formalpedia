-- Prove2me | Theorems.Thm_CertRandQROM_lemma_3_1_trace_dist_le_euclid
-- name    : CertRandQROM.lemma_3_1_trace_dist_le_euclid
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:30:49.548733+00:00
-- url     : https://prove2.me/theorems/e49c5113-4298-480b-9b25-e00f268a476b
-- title:
--   Lemma 3.1 — trace distance of pure states is at most their Euclidean distance
-- statement:
--   For any pure states $|\psi\rangle$ and $|\varphi\rangle$ (unit vectors of $\mathbb C^\iota$, $\iota$ a finite set),
--
--   $$
--   \mathrm{TraceDist}\big(|\psi\rangle,|\varphi\rangle\big)\le\big\||\psi\rangle-|\varphi\rangle\big\|_2 ,
--   $$
--
--   where $\mathrm{TraceDist}(|\psi\rangle,|\varphi\rangle)=\tfrac12\big\||\psi\rangle\langle\psi|-|\varphi\rangle\langle\varphi|\big\|_1$.
--
--   This converts the Euclidean bound of the swapping lemma into a bound on the change of every output probability (equation (22) in the proof of Lemma 7.3).
--
--   **Formalization Note** The trace distance and $|\psi\rangle\langle\psi|$ are the published `CommitOpen.Benign.traceDistance` and `CommitOpen.Benign.pureState`.
--
--   Differences from the source:
--   - encoding: TraceDist(|ψ⟩, |φ⟩) of pure states → traceDistance (½‖·‖₁) of the matrices |ψ⟩⟨ψ|, |φ⟩⟨φ| for unit vectors of ℂ^ι, ι finite; reason: standard meaning of the trace distance of pure states
-- source:
--   Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, Unconditional Certified Randomness without Structure, arXiv:2608.31112 (sha256 b75095a2…), Lemma 3.1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

namespace CertRandQROM

/-- **Lemma 3.1** (Coladangelo, Khurana, Mutreja, Roberts, Slote, Tal, *Unconditional Certified
Randomness without Structure*, arXiv:2608.31112 (sha256 b75095a2…), §3, p.14): for any pure
states `|ψ⟩, |φ⟩`, `TraceDist(|ψ⟩, |φ⟩) ≤ ‖|ψ⟩ − |φ⟩‖₂`.

**Formalization Note** `TraceDist(|ψ⟩, |φ⟩)` is the published
`CommitOpen.Benign.traceDistance` of the density matrices `|ψ⟩⟨ψ|` and `|φ⟩⟨φ|`
(`½‖ρ − σ‖₁`). Pure states are unit vectors of `ℂ^ι` for any finite basis set `ι`. -/
theorem lemma_3_1_trace_dist_le_euclid {ι : Type} [Fintype ι] [DecidableEq ι]
    (ψ φ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    CommitOpen.Benign.traceDistance (CommitOpen.Benign.pureState ψ)
      (CommitOpen.Benign.pureState φ) ≤ ‖ψ - φ‖ := by sorry

end CertRandQROM
