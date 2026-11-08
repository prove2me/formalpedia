-- Prove2me | Theorems.Thm_EntangledPIR_claim_3_8
-- name    : EntangledPIR.claim_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:11:40.118205+00:00
-- url     : https://prove2.me/theorems/38e1286e-8e9d-4b50-a373-7b3973073a70
-- title:
--   Claim 3.8 — the geometric mean bound
-- statement:
--   In the proof of Theorem 3.1(i), for all $s,s'\in\{0,\dots,k\}$,
--
--   $$\|A(\rho_{ss'})\|_1\le\ell^{-(s+s')/2}\sqrt{p_sp_{s'}}.$$
--
--   The bound is the main step of the cut-and-choose bound. It uses that the adversary fixes its state before the positions are chosen.
--
--   Differences from the source:
--   - encoding: finite-dimensional registers and tensor products → finite basis types, `Matrix` on them and `⊗ₖ`; reason: Lean convention; a register is its computational basis, same operators
--   - encoding: the standing hypotheses of the proof of Theorem 3.1(i) → explicit binders: test family, $\rho$ positive semidefinite with trace at most one, $s,s'\le k$; reason: the claim is stated inside that proof; $p_s=\mathrm{Tr}(Q_s\rho)$ as a real part, since it is real on a Hermitian $\rho$
--   - encoding: $\|\cdot\|_1$ of a non-Hermitian operator → `WildeQIT.traceNorm`, defined for every matrix; reason: the Schatten 1-norm
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Claim 3.8, p.16; proof p.17

import Definitions.Def_EntangledPIR_CutChoose
import Definitions.Def_WildeQIT_traceNorm

open Matrix
open scoped ComplexOrder

namespace EntangledPIR

/-- **Claim 3.8**, Mantri, manuscript (Nov. 2026), p.16, proof p.17: for all `s, s′ ∈ {0, …, k}`,
`‖A(ρ_{ss′})‖₁ ≤ ℓ^{-(s+s′)/2} √(p_s p_{s′})`, for a subnormalized state `ρ` of `RB`. The powers of `ℓ` are real
powers. -/
theorem claim_3_8 {k ℓ d : ℕ} (hk : 1 ≤ k) (hd : 1 ≤ d) (hℓ : 2 ≤ ℓ) {E : Fin k × Fin ℓ → Type}
    [∀ c, Fintype (E c)] [∀ c, DecidableEq (E c)]
    (Pi : ∀ c, Matrix (CopyB d E c) (CopyB d E c) ℂ) (hPi : IsTestFamily Pi)
    {R : Type} [Fintype R] [DecidableEq R] (ρ : Matrix (R × AllB d E) (R × AllB d E) ℂ)
    (hρ : ρ.PosSemidef) (hρ1 : ρ.trace.re ≤ 1) (s s' : ℕ) (hs : s ≤ k) (hs' : s' ≤ k) :
    WildeQIT.traceNorm (Amap Pi (onB (Qs Pi s) * ρ * onB (Qs Pi s'))) ≤
      (ℓ : ℝ) ^ (-((s : ℝ) + (s' : ℝ)) / 2) * Real.sqrt (probS Pi ρ s * probS Pi ρ s') := by sorry

end EntangledPIR
