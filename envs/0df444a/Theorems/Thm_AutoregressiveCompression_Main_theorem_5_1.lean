-- Prove2me | Theorems.Thm_AutoregressiveCompression_Main_theorem_5_1
-- name    : AutoregressiveCompression.Main.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:14:56.830709+00:00
-- url     : https://prove2.me/theorems/f32d9d53-2425-43f1-b4db-76c2942dd5b2
-- title:
--   Theorem 5.1 — autoregressive learning ⇔ universal compression of random prefixes (seven equivalent conditions)
-- statement:
--   Fix a finite alphabet Σ with |Σ| ≥ 2 (the standing convention of §4.2), and let 𝒟 = {𝒟ₙ} be any class of distributions over Σ: each 𝒟ₙ is an arbitrary set of distributions on Σ^N with N ≤ n, with real probabilities and no samplability, finiteness or prefix-closure assumption. Prefix(𝒟) is the class over Σ⊥ = Σ ∪ {⊥} whose n-th slice is {Prefix(D) : D ∈ 𝒟ₙ}, where Prefix(D) is the law of X_{≤I} ∘ ⊥^{N−I} for independent X ∼ D and I uniform on {1,…,N}. Then the following are equivalent: (1) 𝒟 admits polynomial-time autoregressive distribution learning; (2) Prefix(𝒟) admits polynomial-time public-coin universal compression; (3) Prefix(𝒟) admits polynomial-time deterministic universal compression; (4) Prefix(𝒟) admits polynomial-time randomized universal compression, i.e. Yao's effective entropy coincides with Shannon entropy on Prefix(𝒟); (5) Prefix(𝒟) admits polynomial-time public-coin universal compression without an efficient decoder; (6) Prefix(𝒟) admits polynomial-time entropy estimation; (7) Prefix(𝒟) admits polynomial-time entropy gap testing.
--
--   Here every algorithm is one finite Turing machine with one polynomial time bound, fixed before the size parameter n, the distribution and the inputs; randomized algorithms read a uniformly random coin string of polynomial length. Autoregressive learning (Definition 4.5) means: on 1ⁿ, 1^{1/ε}, 1^{1/δ} and m = ρ(n,1/ε,1/δ) independent samples, the learner outputs on every input a circuit P with rational P(u,a) ∈ (0,1) and Σₐ P(u,a) = 1 for |u| < N, and with probability ≥ 1−δ the represented law Q_P(z) = ∏ᵢ P(z_{<i}, zᵢ) satisfies KL₂(D‖Q_P) ≤ ε (or, in a learner of the other kind, Δ_tv(D,Q_P) ≤ ε). Public-coin universal compression (Definition 4.7): efficient Enc and Dec sharing a public coin string of length r(n,m) with exact decoding of every block for every coin string and expected codeword length ≤ mH(D) + m^{1−γ} for m ≥ ρ(n), with γ ∈ (0,1); deterministic means r ≡ 0; "without an efficient decoder" means Dec is an arbitrary function. Randomized universal compression (Definitions 4.9–4.10, h = H): independent coins for Enc and Dec, every block decoded with probability ≥ 1 − η(m) for a negligible η, and the same rate. Entropy estimation (Definition 4.12): an estimate E with Pr[E ≤ H(D)+ε] ≥ 1−δ for D in the class and Pr[E ≥ H(Q)−ε] ≥ 1−δ for every Q on Σ^{ℓ(D)}. Entropy gap testing (Definition 4.13): a [0,1]-valued tester and constants a, b > 0 with E_{Q^{⊗m}}[T] − E_{D^{⊗m}}[T] ≥ m^{−b} whenever m ≥ ρ(n) and H(Q) ≥ H(D) + m^{−a}.
--
--   Differences from the source:
--   - encoding: polynomial-time (randomized) algorithms; running time polynomial in n and m (or in the input length) → a Mathlib Turing.FinTM2 machine with bit input and output stacks, halting with the stated output within time.eval(n+m) (resp. time.eval(n+ε⁻¹+δ⁻¹)) steps on every relevant input; coins are a uniformly random input string of polynomial length r(·); reason: standard model of a randomized polynomial-time machine (it reads at most polynomially many coins); the input length is polynomially bounded in, and at least, the stated parameters, so the two time measures agree up to polynomials; the function next to each machine is the output it actually produces
--   - encoding: polynomials ρ, r (sample bound, coin length, threshold) → Polynomial ℕ / MvPolynomial with ℕ coefficients, evaluated at (n,m) or (n,ε⁻¹,δ⁻¹); reason: every polynomial bound is dominated by one with natural coefficients, and an algorithm may ignore extra samples or coins, so the set of admitting classes is unchanged
--   - encoding: hypothesis circuits computing rationals; real-valued estimator and tester outputs → explicit straight-line Boolean circuits (Circuit, with an injective description Circuit.bits) whose output is numerator/denominator wires, read on a one-hot encoding of (u,a); estimates and test values are rationals written by ratBits; reason: finite representations of the source objects; any polynomial-size circuit or polynomial-time real output has such a representation of polynomial length
--   - encoding: ε, δ ∈ (0,1) with ε⁻¹, δ⁻¹ ∈ ℕ → naturals a, b ≥ 2 with ε = 1/a, δ = 1/b, given in unary; reason: same parameter set
--   - encoding: Σ⊥ = Σ ∪ {⊥}; strings of length N; Prefix(D) for ℓ(D) = 0 → Option Σ with ⊥ = none; words Fin N → Σ; the point mass on the empty word (footnote 5); reason: Lean convention; same objects
--   - encoding: randomized Enc and Dec with independent random strings → independent uniform coin strings of polynomial lengths rE(n,m), rD(n,m) supplied as inputs; reason: a decoder running in time polynomial in n and m reads at most that many coins; the tape length r_D(n,m) tells the decoder no more than the O(log m) bits an encoder can add to its codeword, so admitting classes are unchanged
-- source:
--   Shuichi Hirahara, Mikito Nanashima, Autoregressive Distribution Learning and Universal Compression, STOC 2027 submission #793 (October 2026), Theorem 5.1, printed p.21 / PDF p.23; definitions 4.5, 4.7, 4.9, 4.10, 4.12, 4.13, printed pp.17–21 / PDF pp.19–23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/793.pdf

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Tasks

namespace AutoregressiveCompression.Main

/-- Theorem 5.1 (formal version of Theorem 1.2), Hirahara–Nanashima, STOC 2027
submission #793, printed p.21 / PDF p.23. For a finite alphabet `Σ` with `|Σ| ≥ 2`
(§4.2) and every class `𝒟` of distributions over `Σ`, the following are equivalent:
(1) autoregressive learning of `𝒟`; (2) public-coin, (3) deterministic,
(4) randomized (Yao) universal compression of `Prefix(𝒟)`; (5) public-coin
universal compression of `Prefix(𝒟)` without an efficient decoder; (6) entropy
estimation and (7) entropy gap testing for `Prefix(𝒟)`, all in polynomial time. -/
theorem theorem_5_1 {Sym : Type} [Fintype Sym] (hSym : 2 ≤ Fintype.card Sym)
    (𝒟 : DistributionClass Sym) :
    List.TFAE
      [AutoregressiveLearnable 𝒟,
       PublicCoinCompressible 𝒟.prefix,
       DeterministicCompressible 𝒟.prefix,
       RandomizedCompressible 𝒟.prefix,
       PublicCoinCompressibleInefficientDecoder 𝒟.prefix,
       EntropyEstimable 𝒟.prefix,
       EntropyGapTestable 𝒟.prefix] := by sorry

end AutoregressiveCompression.Main
