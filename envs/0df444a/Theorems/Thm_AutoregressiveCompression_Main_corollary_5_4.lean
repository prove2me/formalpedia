-- Prove2me | Theorems.Thm_AutoregressiveCompression_Main_corollary_5_4
-- name    : AutoregressiveCompression.Main.corollary_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:14:58.104826+00:00
-- url     : https://prove2.me/theorems/497d5c05-902b-4273-80ab-f3f850fe9175
-- title:
--   Corollary 5.4 — compression without an efficient decoder gives entropy estimation
-- statement:
--   Let Γ be a finite alphabet with |Γ| ≥ 2 and 𝒞 any class of distributions over Γ. If 𝒞 admits polynomial-time public-coin universal compression without an efficient decoder, then 𝒞 admits polynomial-time entropy estimation.
--
--   Differences from the source:
--   - encoding: polynomial-time (randomized) algorithms; running time polynomial in n and m (or in the input length) → a Mathlib Turing.FinTM2 machine with bit input and output stacks, halting with the stated output within time.eval(n+m) (resp. time.eval(n+ε⁻¹+δ⁻¹)) steps on every relevant input; coins are a uniformly random input string of polynomial length r(·); reason: standard model of a randomized polynomial-time machine (it reads at most polynomially many coins); the input length is polynomially bounded in, and at least, the stated parameters, so the two time measures agree up to polynomials; the function next to each machine is the output it actually produces
--   - encoding: polynomials ρ, r (sample bound, coin length, threshold) → Polynomial ℕ / MvPolynomial with ℕ coefficients, evaluated at (n,m) or (n,ε⁻¹,δ⁻¹); reason: every polynomial bound is dominated by one with natural coefficients, and an algorithm may ignore extra samples or coins, so the set of admitting classes is unchanged
--   - encoding: hypothesis circuits computing rationals; real-valued estimator and tester outputs → explicit straight-line Boolean circuits (Circuit, with an injective description Circuit.bits) whose output is numerator/denominator wires, read on a one-hot encoding of (u,a); estimates and test values are rationals written by ratBits; reason: finite representations of the source objects; any polynomial-size circuit or polynomial-time real output has such a representation of polynomial length
--   - encoding: ε, δ ∈ (0,1) with ε⁻¹, δ⁻¹ ∈ ℕ → naturals a, b ≥ 2 with ε = 1/a, δ = 1/b, given in unary; reason: same parameter set
-- source:
--   Shuichi Hirahara, Mikito Nanashima, Autoregressive Distribution Learning and Universal Compression, STOC 2027 submission #793 (October 2026), Corollary 5.4, printed p.23 / PDF p.25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/793.pdf

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Tasks

namespace AutoregressiveCompression.Main

/-- Corollary 5.4, printed p.23 / PDF p.25. Public-coin universal compression without an efficient decoder implies entropy estimation. -/
theorem corollary_5_4 {Γ : Type} [Fintype Γ] (hΓ : 2 ≤ Fintype.card Γ)
    (𝒞 : DistributionClass Γ) :
    PublicCoinCompressibleInefficientDecoder 𝒞 → EntropyEstimable 𝒞 := by sorry

end AutoregressiveCompression.Main
