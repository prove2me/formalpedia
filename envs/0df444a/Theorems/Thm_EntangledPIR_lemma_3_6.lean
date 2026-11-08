-- Prove2me | Theorems.Thm_EntangledPIR_lemma_3_6
-- name    : EntangledPIR.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:11:05.367131+00:00
-- url     : https://prove2.me/theorems/14e332b8-ae10-4827-b678-408f2755196e
-- title:
--   Lemma 3.6 — average of the acceptance projectors
-- statement:
--   The projectors satisfy
--
--   $$\ell^{-k}\sum_{t\in[\ell]^k}\Pi_t=\sum_{s=0}^k\ell^{-s}Q_s,$$
--
--   and for every $t\in[\ell]^k$, we have $\Pi_t\bigl(1-\sum_{s=0}^kQ_s\bigr)=0$ and $\Pi_tQ_s=E^t_s\Pi_tQ_s$ for $0\le s\le k$.
--
--   This identity expresses that the adversary does not know which copies are tested.
--
--   Differences from the source:
--   - encoding: finite-dimensional registers and tensor products → finite basis types, `Matrix` on them and `⊗ₖ`; reason: Lean convention; a register is its computational basis, same operators
--   - generalization: the projectors of §3 under the standing assumption (3.1) → only that each $\Pi_{i,j}$ is a Hermitian idempotent; reason: the lemma's statement and proof do not use (3.1); this covers the page's family and specializes to it
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Lemma 3.6, p.16

import Definitions.Def_EntangledPIR_CutChoose

open Matrix

namespace EntangledPIR

/-- **Lemma 3.6 (Average of the Acceptance Projectors)**, Mantri, manuscript (Nov. 2026), p.16. The projectors
satisfy `ℓ^{-k} ∑_t Π_t = ∑_{s=0}^k ℓ^{-s} Q_s`, (3.6), and for every `t`, `Π_t (1 − ∑_{s=0}^k Q_s) = 0` and
`Π_t Q_s = E^t_s Π_t Q_s` for `0 ≤ s ≤ k`. The lemma states no hypothesis (3.1), and the `Π_{i,j}` are projectors
on different copies. -/
theorem lemma_3_6 {k ℓ d : ℕ} (hk : 1 ≤ k) (hd : 1 ≤ d) (hℓ : 2 ≤ ℓ) {E : Fin k × Fin ℓ → Type}
    [∀ c, Fintype (E c)] [∀ c, DecidableEq (E c)]
    (Pi : ∀ c, Matrix (CopyB d E c) (CopyB d E c) ℂ) (hH : ∀ c, (Pi c).IsHermitian)
    (hI : ∀ c, Pi c * Pi c = Pi c) :
    ((ℓ : ℂ) ^ k)⁻¹ • ∑ t : Positions k ℓ, PiT Pi t =
        ∑ s ∈ Finset.range (k + 1), ((ℓ : ℂ) ^ s)⁻¹ • Qs Pi s ∧
      ∀ t : Positions k ℓ,
        PiT Pi t * (1 - ∑ s ∈ Finset.range (k + 1), Qs Pi s) = 0 ∧
        ∀ s, s ≤ k → PiT Pi t * Qs Pi s = Ets Pi t s * PiT Pi t * Qs Pi s := by sorry

end EntangledPIR
