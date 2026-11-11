-- Prove2me | Theorems.Thm_AutoregressiveCompression_Main_lemma_5_10
-- name    : AutoregressiveCompression.Main.lemma_5_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:14:52.338558+00:00
-- url     : https://prove2.me/theorems/8609f4b5-995a-4377-a35d-4881d4d996c1
-- title:
--   Lemma 5.10 — autoregressive learning passes to the prefix class
-- statement:
--   Let Σ be a finite alphabet with |Σ| ≥ 2 and 𝒟 any class of distributions over Σ. If 𝒟 admits polynomial-time autoregressive distribution learning, then so does Prefix(𝒟) over Σ⊥.
--
--   Differences from the source:
--   - encoding: polynomial-time (randomized) algorithms; running time polynomial in n and m (or in the input length) → a Mathlib Turing.FinTM2 machine with bit input and output stacks, halting with the stated output within time.eval(n+m) (resp. time.eval(n+ε⁻¹+δ⁻¹)) steps on every relevant input; coins are a uniformly random input string of polynomial length r(·); reason: standard model of a randomized polynomial-time machine (it reads at most polynomially many coins); the input length is polynomially bounded in, and at least, the stated parameters, so the two time measures agree up to polynomials; the function next to each machine is the output it actually produces
--   - encoding: polynomials ρ, r (sample bound, coin length, threshold) → Polynomial ℕ / MvPolynomial with ℕ coefficients, evaluated at (n,m) or (n,ε⁻¹,δ⁻¹); reason: every polynomial bound is dominated by one with natural coefficients, and an algorithm may ignore extra samples or coins, so the set of admitting classes is unchanged
--   - encoding: hypothesis circuits computing rationals; real-valued estimator and tester outputs → explicit straight-line Boolean circuits (Circuit, with an injective description Circuit.bits) whose output is numerator/denominator wires, read on a one-hot encoding of (u,a); estimates and test values are rationals written by ratBits; reason: finite representations of the source objects; any polynomial-size circuit or polynomial-time real output has such a representation of polynomial length
--   - encoding: ε, δ ∈ (0,1) with ε⁻¹, δ⁻¹ ∈ ℕ → naturals a, b ≥ 2 with ε = 1/a, δ = 1/b, given in unary; reason: same parameter set
--   - encoding: Σ⊥ = Σ ∪ {⊥}; strings of length N; Prefix(D) for ℓ(D) = 0 → Option Σ with ⊥ = none; words Fin N → Σ; the point mass on the empty word (footnote 5); reason: Lean convention; same objects
-- source:
--   Shuichi Hirahara, Mikito Nanashima, Autoregressive Distribution Learning and Universal Compression, STOC 2027 submission #793 (October 2026), Lemma 5.10, printed p.28 / PDF p.30; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/793.pdf

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Tasks

namespace AutoregressiveCompression.Main

/-- Lemma 5.10, printed p.28 / PDF p.30. If a class admits autoregressive learning, so does its prefix class over the extended alphabet. -/
theorem lemma_5_10 {Sym : Type} [Fintype Sym] (hSym : 2 ≤ Fintype.card Sym)
    (𝒟 : DistributionClass Sym) :
    AutoregressiveLearnable 𝒟 → AutoregressiveLearnable 𝒟.prefix := by sorry

end AutoregressiveCompression.Main
