-- Prove2me | Theorems.Thm_EntangledPIR_lemma_4_3
-- name    : EntangledPIR.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:09:51.23997+00:00
-- url     : https://prove2.me/theorems/aaa16f82-4be7-4832-8e8d-ca5a2164c69f
-- title:
--   Lemma 4.3 — covariance and completeness of the test
-- statement:
--   Let $g:\{0,1\}^d\to\{0,1\}^m$ and $a\in\{0,1\}^d$.
--
--   1. For all $f,\gamma\in\{0,1\}^d$,
--   $$Z^\gamma_{\mathsf P'}\Pi^a_fZ^\gamma_{\mathsf P'}=\Pi^a_{f\oplus\gamma}.$$
--   2. Suppose that the servers share the Bell pairs of one copy and that A performs its operation with mask $a$ and obtains $e$. Then the joint state, conditioned on $e$, is supported on the range of $1\otimes\Pi^a_e$. In particular, the test with mask $a$ returns $e$ with probability one, whether B performs it before or after the operation of A.
--
--   This is how the test detects a server that copies its address, and why an honest server always passes.
--
--   Differences from the source:
--   - encoding: finite-dimensional registers and tensor products → finite basis types, `Matrix` on them and `⊗ₖ`; reason: Lean convention; a register is its computational basis, same operators
--   - encoding: $\{0,1\}^d$ and $\oplus$ → `Fin d → Bool` and coordinatewise `xor`; reason: Lean convention; same strings
--   - encoding: the joint state with the environment of the measurement, conditioned on $e$, supported on the range → the unnormalized vector $\psi_e$ on the two servers' registers satisfies $(1\otimes\Pi^a_e)\psi_e=\psi_e$; reason: the environment is the tensor factor $|e\rangle$, a function of the branch $e$, and the unnormalized form includes outcomes of probability zero
--   - encoding: the test returns $e$ with probability one, in either order → for $f\ne e$ the branches vanish in both orders, and the probabilities of $f=e$ sum to one in both orders; reason: this is the meaning of the sentence
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Lemma 4.3, p.22

import Definitions.Def_EntangledPIR_testProj

open Matrix

namespace EntangledPIR

/-- **Lemma 4.3 (Covariance and Completeness of the Test)**, Mantri, manuscript (Nov. 2026), p.22.
(i) `Z^γ_{P′} Π^a_f Z^γ_{P′} = Π^a_{f⊕γ}`, (4.4). (ii) In the state `|Φ+⟩^{⊗r}` of one copy, after the
operation of A with mask `a` and outcome `e`, the unnormalized vector `ψ_e` lies in the range of
`1 ⊗ Π^a_e`. In particular, the test with mask `a` returns `e` with probability one, whether B performs it
before or after the operation of A: `(1 ⊗ Π^a_f) ψ_e = 0` for `f ≠ e`, and the other order vanishes as well,
and the probabilities of agreement over `e` sum to one in both orders.

**Formalization Note.** The environment of the measurement of A is the tensor factor `|e⟩`, a function of
the branch `e`, so a statement about `ψ_e` for each `e` is a statement about the joint state with it. -/
theorem lemma_4_3 {d m : ℕ} (g : Bits d → Bits m) (a : Bits d) :
    (∀ f γ : Bits d, (onAddr (pauliZs γ) : Matrix (CopyReg d m) (CopyReg d m) ℂ) * testProj g a f *
        onAddr (pauliZs γ) = testProj g a (bxor f γ)) ∧
    (∀ e : Bits d,
      rightOp (testProj g a e) *ᵥ (leftOp (opKraus g a e) *ᵥ bellCopy d m) =
        leftOp (opKraus g a e) *ᵥ bellCopy d m) ∧
    (∀ e f : Bits d, f ≠ e →
      rightOp (testProj g a f) *ᵥ (leftOp (opKraus g a e) *ᵥ bellCopy d m) = 0 ∧
      leftOp (opKraus g a e) *ᵥ (rightOp (testProj g a f) *ᵥ bellCopy d m) = 0) ∧
    (∑ e, normSq (rightOp (testProj g a e) *ᵥ (leftOp (opKraus g a e) *ᵥ bellCopy d m)) = 1) ∧
    (∑ e, normSq (leftOp (opKraus g a e) *ᵥ (rightOp (testProj g a e) *ᵥ bellCopy d m)) = 1) := by sorry

end EntangledPIR
