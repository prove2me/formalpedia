-- Prove2me | Theorems.Thm_AvgWorstGap_lemma_2_11_counting
-- name    : AvgWorstGap.lemma_2_11_counting
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:50:17.576147+00:00
-- url     : https://prove2.me/theorems/26ee1edf-8cee-421f-bbf6-8a3a1849d76f
-- title:
--   Lemma 2.11 — standard counting argument
-- statement:
--   Let $O$ be an oracle, $y$ a string, and $t,n,\gamma\in\mathbb N$. For $\mu$ any of the complexities $K^O(\cdot\mid y)$, $K^{t,O}(\cdot\mid y)$ and $\mathrm{nK}^{t,O}(\cdot\mid y)$,
--   $$\Pr_{x\sim\{0,1\}^n}\big[\mu(x)<n-\gamma\big]<\frac{1}{2^\gamma}.$$
--   For every $\lambda\in(0,1)$ and $\mu$ either of $\mathrm{pK}^{t,O}_\lambda(\cdot\mid y)$ and $\mathrm{pnK}^{t,O}_\lambda(\cdot\mid y)$,
--   $$\Pr_{x\sim\{0,1\}^n}\big[\mu(x)<n-\gamma\big]<\frac{1}{\lambda\cdot2^\gamma}.$$
--
--   Most strings are incompressible for every one of these measures. This is the source of the lower bounds on complexity used throughout the paper.
--
--   **Formalization Note** The statement covers every oracle and every condition (the paper's "moreover"). $n-\gamma$ is a real number, so for $\gamma>n$ the probability is $0$.
--
--   Differences from the source:
--   - encoding: multi-tape machines over {0,1,⊥} with a fixed standard encoding (details unspecified) → the concrete Machine (alphabet {0,1,⊥,blank}, one-way infinite tapes, one-step oracle answers) and the concrete encoding code; reason: the paper fixes none of these details
--   - reading: programs Π for nK^t and pnK^t → single machine-advice pairs (M, α) run with the guess tape; reason: the composition model of p.13 has no guess tape; the nondeterministic output is defined for the pair model of p.12
--   - encoding: minima over ℕ, log, comparisons with s + log ρ → values in ℕ∞ (⊤ for an empty minimum), Real.logb 2, comparisons in EReal; reason: Lean convention; same instances
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), Lemma 2.11, p.15

import Mathlib
import Definitions.Def_AvgWorstGap_pK
import Definitions.Def_AvgWorstGap_pnK

namespace AvgWorstGap

open NKtLB

/-- **Lemma 2.11 (Standard Counting Argument)** (Goldberg, Hu, Lu, Lyu, Oliveira, arXiv:2610.19162, version of October 30, 2026, p.15):
"For every `t ∈ ℕ`, `µ ∈ {K, K^t, nK^t}`, and every `n, γ ∈ ℕ`, we have
`Pr_{x∼{0,1}^n} [µ(x) < n − γ] < 1/2^γ`. Also, for every `t ∈ ℕ`, `λ ∈ (0, 1)`,
`µ ∈ {pK^t_λ, pnK^t_λ}`, and every `n, γ ∈ ℕ`, we have
`Pr_{x∼{0,1}^n} [µ(x) < n − γ] < 1/(λ · 2^γ)`. Moreover, the inequalities above continue to hold in
the presence of an oracle `O` and when conditioning on a fixed string `y`."

**Formalization Note.** Stated for every oracle `O` and condition `y` (the "moreover"); `K^t` and
`nK^t` with empty randomness, as in `K^t(x | y) = K^t(x | y; ϵ)`. `n − γ` is a real number, so
`γ > n` gives probability `0`; the comparison is in `EReal`. -/
theorem lemma_2_11_counting (O : Set (List Bool)) (y : List Bool) (t n γ : ℕ) :
    prob n (fun x => toEReal (KU O x y) < (((n : ℝ) - γ : ℝ) : EReal)) < 1 / 2 ^ γ ∧
    prob n (fun x => toEReal (Kt O t x y []) < (((n : ℝ) - γ : ℝ) : EReal)) < 1 / 2 ^ γ ∧
    prob n (fun x => toEReal (nKt O t x y []) < (((n : ℝ) - γ : ℝ) : EReal)) < 1 / 2 ^ γ ∧
    ∀ lam : ℝ, 0 < lam → lam < 1 →
      prob n (fun x => toEReal (pK O t lam x y) < (((n : ℝ) - γ : ℝ) : EReal)) <
          1 / (lam * 2 ^ γ) ∧
      prob n (fun x => toEReal (pnK O t lam x y) < (((n : ℝ) - γ : ℝ) : EReal)) <
          1 / (lam * 2 ^ γ) := by sorry

end AvgWorstGap
