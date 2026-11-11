-- Prove2me | Theorems.Thm_AutoregressiveCompression_Main_proposition_4_11
-- name    : AutoregressiveCompression.Main.proposition_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:14:46.352141+00:00
-- url     : https://prove2.me/theorems/c2376618-366d-4d46-8ee3-c5a1da98a19f
-- title:
--   Proposition 4.11 — deterministic ⇒ randomized (Yao) ⇒ public-coin compression
-- statement:
--   Let Γ be a finite alphabet with |Γ| ≥ 2 and 𝒞 any class of distributions over Γ. If 𝒞 admits polynomial-time deterministic universal compression, then it admits polynomial-time randomized universal compression (Yao's effective entropy coincides with Shannon entropy on 𝒞); and if it admits polynomial-time randomized universal compression, then it admits polynomial-time public-coin universal compression.
--
--   Differences from the source:
--   - encoding: polynomial-time (randomized) algorithms; running time polynomial in n and m (or in the input length) → a Mathlib Turing.FinTM2 machine with bit input and output stacks, halting with the stated output within time.eval(n+m) (resp. time.eval(n+ε⁻¹+δ⁻¹)) steps on every relevant input; coins are a uniformly random input string of polynomial length r(·); reason: standard model of a randomized polynomial-time machine (it reads at most polynomially many coins); the input length is polynomially bounded in, and at least, the stated parameters, so the two time measures agree up to polynomials; the function next to each machine is the output it actually produces
--   - encoding: polynomials ρ, r (sample bound, coin length, threshold) → Polynomial ℕ / MvPolynomial with ℕ coefficients, evaluated at (n,m) or (n,ε⁻¹,δ⁻¹); reason: every polynomial bound is dominated by one with natural coefficients, and an algorithm may ignore extra samples or coins, so the set of admitting classes is unchanged
--   - encoding: randomized Enc and Dec with independent random strings → independent uniform coin strings of polynomial lengths rE(n,m), rD(n,m) supplied as inputs; reason: a decoder running in time polynomial in n and m reads at most that many coins; the tape length r_D(n,m) tells the decoder no more than the O(log m) bits an encoder can add to its codeword, so admitting classes are unchanged
-- source:
--   Shuichi Hirahara, Mikito Nanashima, Autoregressive Distribution Learning and Universal Compression, STOC 2027 submission #793 (October 2026), Proposition 4.11, printed p.20 / PDF p.22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/793.pdf

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Tasks

namespace AutoregressiveCompression.Main

/-- Proposition 4.11, Hirahara–Nanashima, STOC 2027 submission #793, printed p.20 / PDF p.22. Deterministic universal compression implies that Yao's effective entropy coincides with Shannon entropy, which in turn implies public-coin universal compression. -/
theorem proposition_4_11 {Γ : Type} [Fintype Γ] (hΓ : 2 ≤ Fintype.card Γ)
    (𝒞 : DistributionClass Γ) :
    (DeterministicCompressible 𝒞 → RandomizedCompressible 𝒞) ∧
      (RandomizedCompressible 𝒞 → PublicCoinCompressible 𝒞) := by sorry

end AutoregressiveCompression.Main
