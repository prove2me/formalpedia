-- Prove2me | Theorems.Thm_AutoregressiveCompression_Main_theorem_6_1
-- name    : AutoregressiveCompression.Main.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:14:49.610705+00:00
-- url     : https://prove2.me/theorems/a4e82cb8-efd1-4647-b334-e2c9b380b7cd
-- title:
--   Theorem 6.1 — public-coin and deterministic universal compression are equivalent
-- statement:
--   Let Γ be a finite alphabet with |Γ| ≥ 2 and 𝒞 any class of distributions over Γ. 𝒞 admits polynomial-time public-coin universal compression if and only if it admits polynomial-time deterministic universal compression.
--
--   Differences from the source:
--   - encoding: polynomial-time (randomized) algorithms; running time polynomial in n and m (or in the input length) → a Mathlib Turing.FinTM2 machine with bit input and output stacks, halting with the stated output within time.eval(n+m) (resp. time.eval(n+ε⁻¹+δ⁻¹)) steps on every relevant input; coins are a uniformly random input string of polynomial length r(·); reason: standard model of a randomized polynomial-time machine (it reads at most polynomially many coins); the input length is polynomially bounded in, and at least, the stated parameters, so the two time measures agree up to polynomials; the function next to each machine is the output it actually produces
--   - encoding: polynomials ρ, r (sample bound, coin length, threshold) → Polynomial ℕ / MvPolynomial with ℕ coefficients, evaluated at (n,m) or (n,ε⁻¹,δ⁻¹); reason: every polynomial bound is dominated by one with natural coefficients, and an algorithm may ignore extra samples or coins, so the set of admitting classes is unchanged
-- source:
--   Shuichi Hirahara, Mikito Nanashima, Autoregressive Distribution Learning and Universal Compression, STOC 2027 submission #793 (October 2026), Theorem 6.1, printed p.33 / PDF p.35; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/793.pdf

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Tasks

namespace AutoregressiveCompression.Main

/-- Theorem 6.1, printed p.33 / PDF p.35. Public-coin and deterministic universal compression are equivalent. -/
theorem theorem_6_1 {Γ : Type} [Fintype Γ] (hΓ : 2 ≤ Fintype.card Γ)
    (𝒞 : DistributionClass Γ) :
    PublicCoinCompressible 𝒞 ↔ DeterministicCompressible 𝒞 := by sorry

end AutoregressiveCompression.Main
