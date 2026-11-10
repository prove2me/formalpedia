-- Prove2me | Theorems.Thm_AvgWorstGap_lemma_3_14_main_technical
-- name    : AvgWorstGap.lemma_3_14_main_technical
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:51:09.846927+00:00
-- url     : https://prove2.me/theorems/4a0bd1c9-94e4-4613-9ca8-36a91a952e85
-- title:
--   Lemma 3.14 — deciding Σ_k^P in time 2^{O(pK^{q(n),O}(x) − K(x))}·poly(n, ℓ)
-- statement:
--   Let $k_0\in\mathbb N$ and let $O$ be a $\Sigma^{\mathrm P}_{k_0}$-complete language. Suppose there are polynomials $\rho$ and $\tau$ with $\mathrm{Gap}_\rho\text{-}\mathrm{MINpKT}^O\in\mathsf{prBPTIME}[\tau(n)]$. Then for every $k\le k_0$, every $L\in\Sigma^{\mathrm P}_k$ and every polynomial $q$ there are a constant $C$ and a randomized algorithm $A$ with the following property. For every $\ell\in\mathbb N$ and every $x\in\{0,1\}^n$, with probability at least $1-2^{-\ell}$ over the internal randomness of $A$, both of the following hold:
--
--   1. $A(x,1^\ell)$ runs in time at most $2^{C\cdot|f(x)|}\cdot C\cdot(n+\ell+1)^C$, where $f(x)=\mathrm{pK}^{q(n),O}(x)-K(x)$;
--   2. $A(x,1^\ell)=1$ if and only if $x\in L$.
--
--   The constant $C$ depends only on $O,\rho,\tau,k,L,q$. In the paper the time bound is $2^{O(\mathrm{pK}^{q(n),O}(x)-K(x))}\cdot\mathrm{poly}(n,\ell)$. The lemma decides $\mathsf{PH}$ languages quickly on every string whose time-bounded complexity is close to its plain complexity, and Lemma 3.13 builds on it.
--
--   **Formalization Note** "With probability at least $1-2^{-\ell}$, $A$ halts within the bound with the correct answer" is stated as follows. Some $T$ not above the bound has $\Pr_{r\in\{0,1\}^T}[A$ halts on $(x,1^\ell)$ within $T$ steps with output $[x\in L]]\ge1-2^{-\ell}$; a run of $T$ steps reads at most $T$ random bits. When $\mathrm{pK}^{q(n),O}(x)=\infty$ the time bound is infinite, and only correctness with that probability is required. $\mathrm{pK}$ has $\lambda=2/3$ and $K$ is plain Kolmogorov complexity.
--
--   Differences from the source:
--   - reading: the bound 2^{O(f)}·poly(n, ℓ) with constants depending only on O, ρ, τ, k, L, q → 2^{C·|f|}·C·(n + ℓ + 1)^C with one C chosen with A, before ℓ and x; reason: O(f) is a quantity of absolute value at most C|f|; C·(n+ℓ+1)^C bounds every poly(n, ℓ)
--   - encoding: "with probability ≥ 1 − 2^{−ℓ}, A runs within the bound and is correct" → some T ≤ bound with Pr_{r ∈ {0,1}^T}[A halts within T steps with output [x ∈ L]] ≥ 1 − 2^{−ℓ}; reason: a run of T steps reads at most T random bits, so this is the probability of the joint event
--   - encoding: Σ_{k0}^P-complete → complete under deterministic polynomial-time many-one reductions; reason: the standard notion
--   - reading: instances (x, 1^s, 1^t, 1^a, 1^b) with any a, b in Defs. 2.9/2.10 → an instance is in YES or NO only if 1 ≤ b ≤ a; reason: b/a and (b−1)/a must lie in [0,1], the domain of Def. 2.2; read literally, (x, 1^0, 1^0, 1^1, 1^0) is in YES ∩ NO (pK^0_0(x) = 0 ≤ 0 and pK^{ρ(1)}_{−1}(x) = 0 ≥ 0 + log 1), so no oracle's problem would be in prBPP
--   - encoding: multi-tape machines over {0,1,⊥} with a fixed standard encoding (details unspecified) → the concrete Machine (alphabet {0,1,⊥,blank}, one-way infinite tapes, one-step oracle answers) and the concrete encoding code; reason: the paper fixes none of these details
--   - encoding: tuples and pairs of strings → the self-delimiting tupleEnc / pairStr; reason: the paper fixes no encoding
--   - encoding: minima over ℕ, log, comparisons with s + log ρ → values in ℕ∞ (⊤ for an empty minimum), Real.logb 2, comparisons in EReal; reason: Lean convention; same instances
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Lemma 3.14, pp.27–28

import Mathlib
import Definitions.Def_AvgWorstGap_GapMINpKT
import Definitions.Def_AvgWorstGap_IsSigmaPComplete

namespace AvgWorstGap

open NKtLB

/-- **Lemma 3.14** (arXiv:2610.19162, version of October 30, 2026, pp.27–28): "Let `k0 ∈ ℕ`, and let `O` be a `Σ^P_{k0}`-complete language.
If there exist polynomials `ρ` and `τ` such that `Gapρ-MINpKT^O ∈ prBPTIME[τ(n)]`, then for every
`k ≤ k0`, `L ∈ Σ^P_k`, and polynomial `q`, there exists a randomized algorithm `A` such that for
every `ℓ ∈ ℕ` and `x ∈ {0, 1}^n`, with probability at least `1 − 2^{−ℓ}` (over the internal
randomness of `A`) both of the following hold. 1. `A(x, 1^ℓ)` runs in time
`2^{O(pK^{q(n),O}(x)−K(x))} · poly(n, ℓ)`, where the constants hidden in `O(·)` and `poly(·)` depend
only on `O, ρ, τ, k, L,` and `q`. 2. `A(x, 1^ℓ) = 1` if and only if `x ∈ L`."

**Formalization Note.** The hidden constants are one `C`, chosen with `A` before `ℓ` and `x`; the
time bound is `2^{C·|f|} · C · (n + ℓ + 1)^C` with `f = pK^{q(n),O}(x) − K(x)` (`O(f)` is a
quantity of absolute value at most `C|f|`). The joint event "halts within the bound with output
`[x ∈ L]`" has probability `≥ 1 − 2^{−ℓ}`: some `T` not above the bound has
`Pr_{r ∈ {0,1}^T}[A halts on (x, 1^ℓ) within T steps with output [x ∈ L]] ≥ 1 − 2^{−ℓ}` (a run of
`T` steps reads at most `T` random bits). When `pK^{q(n),O}(x) = ∞` the bound is `∞` and only
correctness with that probability is required. `pK` has `λ = 2/3`; `K` is plain Kolmogorov
complexity; `(x, 1^ℓ)` is `tupleEnc`. -/
theorem lemma_3_14_main_technical (k₀ : ℕ) (O : Set (List Bool)) (hO : IsSigmaPComplete k₀ O)
    (hGap : ∃ ρ τ : Polynomial ℕ,
      InPrBPTIME (GapMINpKT O (fun n => ρ.eval n)) (fun n => τ.eval n)) :
    ∀ k ≤ k₀, ∀ L : Set (List Bool), InSigmaP k L → ∀ q : Polynomial ℕ,
      ∃ (C : ℕ) (A : Machine), ∀ (ℓ : ℕ) (x : List Bool), ∃ T : ℕ,
        (∀ s κ : ℕ, pK O (q.eval x.length) (2 / 3) x [] = (s : ℕ∞) → K x = (κ : ℕ∞) →
          (T : ℝ) ≤ (2 : ℝ) ^ ((C : ℝ) * |(s : ℝ) - κ|) * C * ((x.length : ℝ) + ℓ + 1) ^ C) ∧
        1 - (2 : ℝ)⁻¹ ^ ℓ ≤ prob T (fun r =>
          HaltsWithBit A ∅ ⟨tupleEnc [x, unary ℓ], [], [], r⟩ T (x ∈ L)) := by sorry

end AvgWorstGap
