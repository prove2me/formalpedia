-- Prove2me | Theorems.Thm_EntangledPIR_claim_C_4
-- name    : EntangledPIR.claim_C_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:15:59.230829+00:00
-- url     : https://prove2.me/theorems/68ae46fe-636f-4ef1-b7f4-101b4f2cb48e
-- title:
--   Claim C.4 — the view of A right after step 5(a)
-- statement:
--   Fix an initial state of the servers and a strategy of A, and let B and the client follow Protocol 1. For each $(a,e)$, let $\zeta^{a,e}_x=R^a_x(A(\rho_{a,e}))$. There are a subnormalized state $\sigma_\perp$ and channels $\Gamma_{a,e}$, none of which depends on $x$, such that the view of A right after step 5(a) is
--
--   $$\mathrm{View}_{\mathsf A}(x)=\sigma_\perp+\sum_{a,e}\Gamma_{a,e}\bigl(\zeta^{a,e}_x\bigr).$$
--
--   This writes the view of A as a term on abort plus images of the states of the cut-and-choose bound.
--
--   Differences from the source:
--   - encoding: finite-dimensional registers and tensor products → finite basis types, `Matrix` on them and `⊗ₖ`; reason: Lean convention; a register is its computational basis, same operators
--   - encoding: instruments, strategies and rounds of §2.1 → Kraus operators with a finite index, `Strategy` per round, the four-round schedule of `clientStep`, messages as bit lists with a bounded alphabet; reason: every finite-dimensional instrument has a Kraus form; over-long messages, all rejected alike, are represented by strings of length `msgBound`; Figure 4 fixes the order of the messages
--   - encoding: the view right after step 5(a) → `viewAMid … 3`, the state after three rounds with the client's message of round 3 in a classical register; reason: step 5(a) is that message; the instrument of A in round 3 comes after it
--   - encoding: channels $\Gamma_{a,e}$ → maps with a trace-preserving Kraus form (`IsChannel`); reason: the definition of a channel in finite dimension
--   - encoding: the registers holding $(a,e)$ in $\mathsf R$ → the family `rhoAE … a e` on `SA.Reg 1 × Copies`, without those classical registers, which $\Gamma_{a,e}$ writes; reason: the projection onto a classical value is the same data; $\Gamma_{a,e}$ depends on $(a,e)$
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Claim C.4, p.59

import Definitions.Def_EntangledPIR_zetaAE

open Matrix
open scoped ComplexOrder

namespace EntangledPIR

/-- **Claim C.4**, Mantri, manuscript (Nov. 2026), p.59. Fix an initial state and a strategy of A, with B and the
client following the protocol. There are a subnormalized state `σ_⊥` and channels `Γ_{a,e}`, none of which depends
on `x`, such that the view of A right after step 5(a) is `View_A(x) = σ_⊥ + ∑_{a,e} Γ_{a,e}(ζ^{a,e}_x)`, (C.2).

**Formalization Note.** Step 5(a) is the client's message of round `3` (`viewAMid … 3`). The existential precedes
the index. -/
theorem claim_C_4 {n m : ℕ} (lam : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hlam : 1 ≤ lam)
    (F : Bits n → Bits m) (SA : Strategy (msgBound n m lam)) (RB0 : Type) [Fintype RB0] [DecidableEq RB0]
    (ρ₀ : Matrix (SA.Reg 0 × (Copies n m lam × RB0)) (SA.Reg 0 × (Copies n m lam × RB0)) ℂ)
    (hρ : ρ₀.PosSemidef) (hρ1 : ρ₀.trace = 1) :
    ∃ (σ : Matrix ((Transcript (msgBound n m lam) 3 × BitStr (msgBound n m lam)) × SA.Reg 3)
          ((Transcript (msgBound n m lam) 3 × BitStr (msgBound n m lam)) × SA.Reg 3) ℂ)
      (Γ : (a e : CopyIdx (shareCount n lam) → Bits (queryLen n lam)) →
        Matrix (Positions (shareCount n lam) 4 × (SA.Reg 1 × ShareVec (shareCount n lam) (queryLen n lam)))
            (Positions (shareCount n lam) 4 × (SA.Reg 1 × ShareVec (shareCount n lam) (queryLen n lam))) ℂ →
          Matrix ((Transcript (msgBound n m lam) 3 × BitStr (msgBound n m lam)) × SA.Reg 3)
            ((Transcript (msgBound n m lam) 3 × BitStr (msgBound n m lam)) × SA.Reg 3) ℂ),
      σ.PosSemidef ∧ σ.trace.re ≤ 1 ∧ (∀ a e, IsChannel (Γ a e)) ∧
      ∀ x : Bits n,
        viewAMid (n := n) (m := m) (lam := lam) SA (honestB lam F RB0) ρ₀ 3 x =
          σ + ∑ a, ∑ e, Γ a e (zetaAE lam F SA RB0 ρ₀ a e x) := by sorry

end EntangledPIR
