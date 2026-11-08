-- Prove2me | Theorems.Thm_EntangledPIR_lemma_4_4
-- name    : EntangledPIR.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:10:01.649607+00:00
-- url     : https://prove2.me/theorems/419adc9f-cd2c-4103-bb5e-05d4944e0bcf
-- title:
--   Lemma 4.4 — uniformity and independence of the address
-- statement:
--   Let $g:\{0,1\}^d\to\{0,1\}^m$ and $a,e\in\{0,1\}^d$.
--
--   1. For every nonzero $\gamma$ and every $q\in\{0,1\}^d$,
--   $$\Pi^a_eZ^\gamma_{\mathsf P'}\Pi^a_e=0,\qquad \Pi^a_e|q\rangle\langle q|_{\mathsf P'}\Pi^a_e=2^{-d}\Pi^a_e.$$
--   2. For every register $\mathsf R$ and every state $\theta$ of $\mathsf{RB}$ supported on the range of $1\otimes\Pi^a_e$, a measurement of $\mathsf P'$ in the computational basis gives an outcome that is uniformly random and independent of $\mathsf R$. In particular, for every initial state and every strategy of A, if A receives the mask $a$ and reports $e$ and the test returns $e$ with nonzero probability, then, conditioned on this outcome, the same measurement gives an outcome uniformly random and independent of all registers of A, also after any later channel of A.
--
--   Part 1 shows that the test projectors satisfy hypothesis (3.1) of the cut-and-choose bound.
--
--   Differences from the source:
--   - encoding: finite-dimensional registers and tensor products → finite basis types, `Matrix` on them and `⊗ₖ`; reason: Lean convention; a register is its computational basis, same operators
--   - encoding: $\{0,1\}^d$ and $\oplus$ → `Fin d → Bool` and coordinatewise `xor`; reason: Lean convention; same strings
--   - encoding: the outcome is uniformly random and independent of $\mathsf R$ → $\mathrm{Tr}_{\mathsf B}[(1\otimes|q\rangle\langle q|_{\mathsf P'})\theta]=2^{-d}\mathrm{Tr}_{\mathsf B}\theta$ for all $q$; reason: the proof states this identity (p.23); it is this independence for operators
--   - generalization: a state $\theta$ supported on the range; the state produced by an initial state and a strategy of A, conditioned on the test, normalized, after a later channel of A → any operator $\theta$ with $(1\otimes\Pi)\theta=\theta=\theta(1\otimes\Pi)$; the operator $(1\otimes\Pi^a_e)\tau(1\otimes\Pi^a_e)$ for any operator $\tau$ on $\mathsf{RB}$, unnormalized, after any Kraus channel on $\mathsf R$; reason: every such state is an instance with $\mathsf R$ all registers of A, including those that hold $a,e$; dividing by the nonzero probability gives the conditioned statement
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Lemma 4.4, pp.22–23

import Definitions.Def_EntangledPIR_testProj
import Definitions.Def_WildeQIT_partialTrace

open Matrix
open scoped Kronecker

namespace EntangledPIR

/-- **Lemma 4.4 (Uniformity and Independence of the Address)**, Mantri, manuscript (Nov. 2026), pp.22–23.
(i) (4.5): for every nonzero `γ` and every `q`, `Π^a_e Z^γ_{P′} Π^a_e = 0` and
`Π^a_e |q⟩⟨q|_{P′} Π^a_e = 2^{-d} Π^a_e`. (ii) For every register `R` and every operator `θ` on `RB` in the
range of `1 ⊗ Π^a_e`, the outcome `q` of the measurement of `P′` is uniform and independent of `R`:
`Tr_B[(1 ⊗ |q⟩⟨q|_{P′}) θ] = 2^{-d} Tr_B θ`. In particular (second sentence of (ii)), for every state `τ` of
`RB`, with `θ = (1 ⊗ Π^a_e) τ (1 ⊗ Π^a_e)` the part on which the test returns `e`, and every later channel of
the holder of `R`, in Kraus form `K_c`, the same holds for `θ` after this channel.

**Formalization Note.** The second sentence of (ii) speaks of the state produced by a strategy of A. Every
such state, conditioned on the mask and the report, is a `τ` here, with `R` all registers of A, so this form
implies it. -/
theorem lemma_4_4 {d m : ℕ} (g : Bits d → Bits m) (a e : Bits d) :
    (∀ γ : Bits d, γ ≠ bzero d →
      testProj g a e * onAddr (pauliZs γ) * testProj g a e = 0) ∧
    (∀ q : Bits d,
      testProj g a e * onAddr (basisProj q) * testProj g a e =
        ((2 : ℂ) ^ d)⁻¹ • (testProj g a e : Matrix (CopyReg d m) (CopyReg d m) ℂ)) ∧
    (∀ (R : Type) [Fintype R] [DecidableEq R]
      (θ : Matrix (R × CopyReg d m) (R × CopyReg d m) ℂ),
      ((1 : Matrix R R ℂ) ⊗ₖ testProj g a e) * θ = θ →
      θ * ((1 : Matrix R R ℂ) ⊗ₖ testProj g a e) = θ → ∀ q : Bits d,
        WildeQIT.partialTraceRight (((1 : Matrix R R ℂ) ⊗ₖ onAddr (basisProj q)) * θ) =
          ((2 : ℂ) ^ d)⁻¹ • WildeQIT.partialTraceRight θ) ∧
    (∀ (R R' ι : Type) [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R'] [Fintype ι]
      (τ : Matrix (R × CopyReg d m) (R × CopyReg d m) ℂ) (K : ι → Matrix R' R ℂ),
      ∑ c, (K c)ᴴ * K c = 1 → ∀ q : Bits d,
        let θ := ((1 : Matrix R R ℂ) ⊗ₖ testProj g a e) * τ *
          ((1 : Matrix R R ℂ) ⊗ₖ testProj g a e)
        let θ' : Matrix (R' × CopyReg d m) (R' × CopyReg d m) ℂ :=
          ∑ c, (K c ⊗ₖ (1 : Matrix (CopyReg d m) (CopyReg d m) ℂ)) * θ *
            (K c ⊗ₖ (1 : Matrix (CopyReg d m) (CopyReg d m) ℂ))ᴴ
        WildeQIT.partialTraceRight (((1 : Matrix R' R' ℂ) ⊗ₖ onAddr (basisProj q)) * θ') =
          ((2 : ℂ) ^ d)⁻¹ • WildeQIT.partialTraceRight θ') := by sorry

end EntangledPIR
