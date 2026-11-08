-- Prove2me | Theorems.Thm_EntangledPIR_claim_3_7
-- name    : EntangledPIR.claim_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:11:55.094124+00:00
-- url     : https://prove2.me/theorems/ba95abbe-e34b-4e2d-9a7f-6fbd0523a5cc
-- title:
--   Claim 3.7 — the $(s,s')$ term below the threshold
-- statement:
--   In the proof of Theorem 3.1(i), with (3.1), privacy threshold $\lambda$ and a subnormalized state $\rho$ of $\mathsf{RB}$: if $s+s'\le\lambda$, then
--
--   $$R_x\bigl(A(\rho_{ss'})\bigr)=R_{x'}\bigl(A(\rho_{ss'})\bigr)\quad\text{for all }x,x',$$
--
--   where $\rho_{ss'}=Q_s\rho Q_{s'}$.
--
--   Differences from the source:
--   - encoding: finite-dimensional registers and tensor products → finite basis types, `Matrix` on them and `⊗ₖ`; reason: Lean convention; a register is its computational basis, same operators
--   - encoding: the standing hypotheses of the proof of Theorem 3.1(i) → explicit binders: test family, threshold, $\rho$ positive semidefinite with trace at most one, $s,s'\le k$; reason: the claim is stated inside that proof
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Claim 3.7, p.16

import Definitions.Def_EntangledPIR_CutChoose

open Matrix
open scoped ComplexOrder

namespace EntangledPIR

/-- **Claim 3.7**, Mantri, manuscript (Nov. 2026), p.16, in the proof of Theorem 3.1(i), under its hypotheses:
(3.1) and privacy threshold `λ`, for a subnormalized state `ρ` of `RB`. If `s + s′ ≤ λ`, then
`R_x(A(ρ_{ss′})) = R_{x′}(A(ρ_{ss′}))` for all `x, x′`, where `ρ_{ss′} = Q_s ρ Q_{s′}`, (3.7). -/
theorem claim_3_7 {k ℓ d : ℕ} (hk : 1 ≤ k) (hd : 1 ≤ d) (hℓ : 2 ≤ ℓ) {E : Fin k × Fin ℓ → Type}
    [∀ c, Fintype (E c)] [∀ c, DecidableEq (E c)]
    (Pi : ∀ c, Matrix (CopyB d E c) (CopyB d E c) ℂ) (hPi : IsTestFamily Pi)
    (lam : ℕ) {X : Type} [Fintype X] (mu : X → ShareVec k d → ℝ) (hmu : IsShareDistribution mu)
    (hthr : HasPrivacyThreshold mu lam)
    {R : Type} [Fintype R] [DecidableEq R] (ρ : Matrix (R × AllB d E) (R × AllB d E) ℂ)
    (hρ : ρ.PosSemidef) (hρ1 : ρ.trace.re ≤ 1) (s s' : ℕ) (hs : s ≤ k) (hs' : s' ≤ k)
    (hss : s + s' ≤ lam) (x x' : X) :
    Rmap (R := R) (mu x) (Amap Pi (onB (Qs Pi s) * ρ * onB (Qs Pi s'))) =
      Rmap (R := R) (mu x') (Amap Pi (onB (Qs Pi s) * ρ * onB (Qs Pi s'))) := by sorry

end EntangledPIR
