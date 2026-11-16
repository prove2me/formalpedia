-- Prove2me | Theorems.Thm_AlgoPFR_Supplement_theorem_7_1_quadratic_goldreich_levin
-- name    : AlgoPFR.Supplement.theorem_7_1_quadratic_goldreich_levin
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T22:36:59.461907+00:00
-- url     : https://prove2.me/theorems/189977fa-2fff-4897-9e99-a48f1b12070a
-- title:
--   Theorem 7.1 — quadratic Goldreich–Levin: from oracle access to $f$ with $\|f\|_{U^3}\ge\varepsilon$, a quadratic $q$ with $\mathbb E f(-1)^q\ge c_1\varepsilon^{c_2}$
-- statement:
--   There are one randomized program and constants $c_1,c_2>0$, $C$, $c$ such that the following holds for every $n$, every $f:\mathbb F_2^n\to[-1,1]$ and all reals $\varepsilon,\delta>0$. The program has oracle access to $f$ and either outputs a quadratic polynomial $q$ over $\mathbb F_2$ or $\bot$.
--
--   1. **Completeness.** If $\|f\|_{U^3}\ge\varepsilon$, then with probability at least $1-\delta$ it outputs a quadratic $q$ with
--   $$\mathbb E_x\bigl[f(x)(-1)^{q(x)}\bigr]\ge c_1\varepsilon^{c_2}.$$
--   2. **Soundness.** For every such $f$, including those with $\|f\|_{U^3}<\varepsilon$, the probability that it outputs a quadratic $q$ with $\mathbb E_x[f(x)(-1)^{q(x)}]<c_1\varepsilon^{c_2}/2$ is at most $\delta$.
--   3. **Cost.** On every run it halts, outputs $\bot$ or a quadratic, and uses at most
--   $$C\bigl(n+1/\varepsilon+\lceil\log(1/\delta)\rceil+2\bigr)^{c}$$
--   queries and log-cost time.
--
--   This is the polynomial-time quadratic Goldreich–Levin theorem, which the source derives from its algorithmic PFR theorem; earlier versions had quasi-polynomial dependence on $1/\varepsilon$.
--
--   **Formalization Note** Logarithms are base 2. The oracle for the real-valued $f$ is the density coin of `AlgoPFR.Machine` with rate $(1+f(x))/2$: each query on $x$ returns a fresh random bit, i.e. a $\pm1$ value with mean $f(x)$ (the rounding of Lemma 7.7). The program reads $n$, $\lceil1/\varepsilon\rceil$, the bit $[\varepsilon\le1]$ and $\lceil\log(1/\delta)\rceil$. Outputs are encoded as in `AlgoPFR.Supplement.Quad`.
--
--   Differences from the source:
--
--   - generalization: oracle access to f : F₂ⁿ → [−1, 1] (exact values) → each query on x returns an independent random bit with mean (1 + f(x))/2 (density coin of the base machine); reason: the RAM holds naturals; one exact value and one uniform simulate a query, so the theorem in this model gives the exact-value version (Lemma 7.7's rounding)
--   - generalization: the algorithm knows ε and δ → it reads only ⌈1/ε⌉₊, the bit [ε ≤ 1] and ⌈log₂(1/δ)⌉₊; reason: less input information, so a stronger existence claim; the bit lets the program output ⊥ when ε > 1, where completeness is vacuous
--   - generalization: uses poly(n, 1/ε, log 1/δ) queries and time → C(n + 1/ε + ⌈log₂(1/δ)⌉₊ + 2)^c queries and log-cost time on every tape whose uniforms lie in [0, 1), constants before n, f, ε, δ; reason: the stronger reading: the proof truncates every trial; the ceiling keeps the bound positive for δ ≥ 1
--   - reading: a quadratic form q → a polynomial of degree ≤ 2 over F₂ with linear and constant terms; reason: Theorem 1.3, Lemma 7.7 and Claim 7.6 say 'quadratic polynomial' and output a constant and a linear phase
--   - encoding: either outputs a quadratic form q or ⊥ → on every run the output is [0] or encodeQuad q; reason: output encoding on the RAM
--   - encoding: the probability of outputting a bad q is at most δ → the complement event has inner measure at least 1 − δ; reason: inner measure, as in the base mission
--   - encoding: a randomized algorithm and 'time' → a program of the randomized log-cost oracle RAM of AlgoPFR.Machine; reason: the source names no model; the base mission fixes this one
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Theorem 7.1, p.47 (proof: §7, pp.47–52; Lemma 7.7, p.51)

import Mathlib
import Definitions.Def_AlgoPFR_Machine
import Definitions.Def_AlgoPFR_Supplement_Quad
import Definitions.Def_AlgoPFR_Supplement_gowersU3

set_option autoImplicit false

open scoped ENNReal

namespace AlgoPFR

namespace Supplement

/-- **Theorem 7.1 (quadratic Goldreich–Levin).** Arunachalam, Dutt, Grewal, Gupte, *Marton's
conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…), p.47: let `ε, δ > 0`. There exist
universal constants `c₁, c₂ > 0` and a randomized algorithm which, given oracle access to a function
`f : F₂ⁿ → [−1, 1]`, either outputs a quadratic form `q` or `⊥`, satisfying
* completeness: if `‖f‖_{U³} ≥ ε`, then with probability at least `1 − δ` it outputs a quadratic `q`
  with `E_x[f(x)(−1)^{q(x)}] ≥ c₁ ε^{c₂}`;
* soundness: for every input `f`, the probability of outputting a quadratic `q` with
  `E_x[f(x)(−1)^{q(x)}] < c₁ ε^{c₂} / 2` is at most `δ`.
The algorithm uses `poly(n, 1/ε, log 1/δ)` queries and time.

**Formalization Note.** One program and the constants `c₁, c₂, C, c` come before `n, f, ε, δ`. The
oracle for the real-valued `f` is the base machine's density coin with rate `(1 + f(x))/2`: each query on
`x` returns an independent bit with mean `(1 + f(x))/2`, i.e. a `±1` value with mean `f(x)`. This is the
randomized rounding of Lemma 7.7, p.51 ("each new query to f̃ uses one query to f"), and it is simulated
by one query to an oracle returning `f(x)` and one uniform, so the theorem in this model implies it for
exact-value oracles. The program reads `[n, ⌈1/ε⌉₊, [ε ≤ 1], ⌈log₂(1/δ)⌉₊]`: a RAM holds naturals, and the
bit `[ε ≤ 1]` lets the program output `⊥` when `ε > 1`, where completeness is vacuous (`‖f‖_{U³} ≤ 1`)
but soundness is not. Outputs are `[0]` for `⊥` and `encodeQuad q` for `q`; on every run the output is
one of these. Soundness is stated as "with probability at least `1 − δ` the output is not a quadratic of
correlation `< c₁ε^{c₂}/2`" (inner-measure form). The resource bound holds on every tape whose
uniforms lie in `[0, 1)`; the sample stream of the base machine is unused (its law is arbitrary, here
uniform on `F₂ⁿ`). -/
theorem theorem_7_1_quadratic_goldreich_levin :
    ∃ (P : Program) (c₁ c₂ C : ℝ) (c : ℕ), 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (n : ℕ) (f : Vec n → ℝ) (ε δ : ℝ), (∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) → 0 < ε → 0 < δ →
      (∀ ω : Tape n, (∀ k, ω.2.2 k ∈ Set.Ico (0 : ℝ) 1) →
        HaltsWithin n P (fun x => (1 + f x) / 2)
            [n, ⌈1 / ε⌉₊, if ε ≤ 1 then 1 else 0, ⌈Real.logb 2 (1 / δ)⌉₊] ω
            (C * ((n : ℝ) + 1 / ε + (⌈Real.logb 2 (1 / δ)⌉₊ : ℝ) + 2) ^ c) ∧
          ∃ o, Outputs n P (fun x => (1 + f x) / 2)
              [n, ⌈1 / ε⌉₊, if ε ≤ 1 then 1 else 0, ⌈Real.logb 2 (1 / δ)⌉₊] ω o ∧
            (o = botOutput ∨ ∃ q : Quad n, o = encodeQuad q)) ∧
      (ε ≤ gowersU3 f →
        ProbAtLeast (tapeMeasure (PMF.uniformOfFintype (Vec n)))
          {ω | ∃ q : Quad n, Outputs n P (fun x => (1 + f x) / 2)
              [n, ⌈1 / ε⌉₊, if ε ≤ 1 then 1 else 0, ⌈Real.logb 2 (1 / δ)⌉₊] ω (encodeQuad q) ∧
            c₁ * ε ^ c₂ ≤ corr f q} (1 - δ)) ∧
      ProbAtLeast (tapeMeasure (PMF.uniformOfFintype (Vec n)))
        {ω | ¬ ∃ q : Quad n, Outputs n P (fun x => (1 + f x) / 2)
            [n, ⌈1 / ε⌉₊, if ε ≤ 1 then 1 else 0, ⌈Real.logb 2 (1 / δ)⌉₊] ω (encodeQuad q) ∧
          corr f q < c₁ * ε ^ c₂ / 2} (1 - δ) := by sorry

end Supplement

end AlgoPFR
