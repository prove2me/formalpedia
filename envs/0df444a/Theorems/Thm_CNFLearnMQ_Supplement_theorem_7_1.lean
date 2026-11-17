-- Prove2me | Theorems.Thm_CNFLearnMQ_Supplement_theorem_7_1
-- name    : CNFLearnMQ.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:06:56.912479+00:00
-- url     : https://prove2.me/theorems/1ce88d7a-7531-48ff-b672-b0e670263c72
-- title:
--   Theorem 7.1 — sample-only lower bounds for $(k,d)$-CNFs from junta-learning hardness
-- statement:
--   Fix a real $t>0$. For an integer $r\ge1$ set $s=\lceil 2r/t\rceil$, $k=r+s$ and $d=2^r$.
--
--   1. For all sufficiently large $r$ (depending on $t$) these parameters satisfy the local lemma condition
--   $$k\ \ge\ \Bigl(1+\frac1t\Bigr)\log d+2\log k+t-3\log t+5. \tag{14}$$
--   2. Assuming Hypothesis 1.5, for every constant $C>0$ and every sufficiently large fixed $r\ge r_0(C,t)$, no randomized algorithm achieves the following guarantee in time $O_r(n^C)\,\mathrm{poly}(1/\varepsilon)$: for all integers $n\ge k$ and all $\varepsilon\in(0,1/8)$, given only i.i.d. samples from $\mu_\Phi$ for any satisfiable $n$-variable $(k,d)$-CNF formula $\Phi$, output an efficiently computable $H:\{0,1\}^n\to\{0,1\}$ such that, with probability at least $2/3$, $\Omega(H)\ne\emptyset$ and $d_{\mathrm{TV}}(\mu_\Phi,\mu_H)\le\varepsilon$.
--   3. Assuming Hypothesis 1.6, there is a constant $c'=c'(t)>0$ such that for every sufficiently large fixed $r\ge r_0(t)$ no randomized algorithm achieves this guarantee in time $O_r(n^{c'k})\,\mathrm{poly}(1/\varepsilon)$.
--
--   The running-time bounds include evaluating $H$ on any input. Both conclusions already hold when the accuracy is fixed at $\varepsilon=2^{-s-4}$, independently of $n$; both the range version and the fixed-accuracy version are stated. Together with Theorem 5.1 this shows that membership queries are what make the polynomial running time with a fixed exponent possible in the local lemma regime.
--
--   Differences from the source:
--   - encoding: randomized algorithm; running time including evaluating $H$ on any input → a `SampleMachine` (finite control, finitely many stacks, unit cost per step, fair coins, a sample oracle); the learning run and every evaluation of $H$ each within the time bound; the same model in Hypotheses 1.5–1.6; reason: the paper fixes no machine model; bounding both parts by the bound instead of their sum is a factor 2 absorbed by $O_r$
--   - encoding: time $O_r(n^C)\,\mathrm{poly}(1/\varepsilon)$ (resp. $O_r(n^{c'k})\,\mathrm{poly}(1/\varepsilon)$) → a constant $K$ and a real polynomial $p$, chosen after $r$ and before $n,\varepsilon,\Phi$, with time at most $K n^C p(1/\varepsilon)$ for all $n\ge k$ and all admissible $\varepsilon$; reason: the paper's reading of $O_r$ for fixed $r$; worst case, as in the proof (p.43)
--   - generalization: accuracy $\varepsilon\in(0,1/8)$ (resp. $\varepsilon=2^{-s-4}$) given to the learner → rational $\varepsilon$, handed to the machine as numerator and denominator (with $n,k,d$) in binary; the guarantee is required only at these $\varepsilon$; reason: a machine input is finite; requiring the guarantee at fewer accuracies enlarges the class of learners shown not to exist, so the Lean statement implies the source's
--   - encoding: Hypotheses 1.5–1.6, a junta learner given only labeled examples → the machine is also handed $N$ in binary, and an example is the bit string $X_1\dots X_N f(X)$; reason: $N$ is the length of any one example, which a machine reads in $O(N\log N)$ steps, so the two classes of learners coincide up to an overhead absorbed by $O_r(N^C)$ (resp. $O_r(N^{cr})$ for large $r$)
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Theorem 7.1, pp.40–41; Hypotheses 1.5, 1.6, p.5

import Mathlib
import Definitions.Def_CNFLearnMQ_Supplement_CNFGuarantee
import Definitions.Def_CNFLearning873_Valiant_Thresholds

set_option autoImplicit false

namespace CNFLearnMQ.Supplement

open CNFLearning873.Valiant CNFLearnMQ

/-- Theorem 7.1 (sample-only lower bound), pp.40–41 (Feng, Yu, Zhang, *Learning CNF Formulas with
Uniform Random Solutions and Membership Queries*, STOC 2027 submission (manuscript sha256
519ee6d4…)). Fix a real `t > 0`. For an integer `r ≥ 1` set `s = ⌈2r/t⌉`, `k = r + s`, `d = 2^r`.
1. (14) For all sufficiently large `r` (depending on `t`),
   `k ≥ (1 + 1/t) log d + 2 log k + t − 3 log t + 5`.
2. Assuming Hypothesis 1.5, for every constant `C > 0` and every sufficiently large fixed
   `r ≥ r₀(C, t)`, no randomized algorithm achieves the guarantee (for all `n ≥ k` and all
   `ε ∈ (0, 1/8)`, from i.i.d. samples of `µ_Φ` for any satisfiable `n`-variable `(k, d)`-CNF `Φ`,
   output `H` with, with probability at least `2/3`, `Ω(H) ≠ ∅` and `d_TV(µ_Φ, µ_H) ≤ ε`) in time
   `O_r(n^C)·poly(1/ε)`, evaluation of `H` on any input included; nor at the fixed accuracy
   `ε = 2^{−s−4}`.
3. Assuming Hypothesis 1.6, there is a constant `c′ = c′(t) > 0` such that for every sufficiently
   large fixed `r ≥ r₀(t)` no randomized algorithm achieves this guarantee in time
   `O_r(n^{c′k})·poly(1/ε)`; nor at the fixed accuracy `ε = 2^{−s−4}`.

**Formalization Note** "Randomized algorithm" and "time" are those of `SampleMachine`, the same
model as in the hypotheses. "In time `O_r(n^C) poly(1/ε)`" is a constant `K` and a polynomial `p`,
chosen after `r` and before `n, ε, Φ`, with time at most `K·n^C·p(1/ε)`. `log` is base 2 (the
published `LLLCondition`, which is (14)). Accuracies are rationals; this only enlarges the class of
learners shown not to exist. -/
theorem theorem_7_1 (t : ℝ) (ht : 0 < t) :
    (∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r → LLLCondition (kParam t r) (dParam r) t) ∧
    (Hypothesis_1_5 → ∀ C : ℝ, 0 < C → ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
      (¬ ∃ (M : SampleMachine) (K : ℝ) (p : Polynomial ℝ),
          CNFGuarantee M (kParam t r) (dParam r) {ε : ℚ | 0 < ε ∧ ε < 1 / 8}
            (fun n ε => K * (n : ℝ) ^ C * p.eval (1 / ε))) ∧
      (¬ ∃ (M : SampleMachine) (K : ℝ) (p : Polynomial ℝ),
          CNFGuarantee M (kParam t r) (dParam r) {1 / 2 ^ (sParam t r + 4)}
            (fun n ε => K * (n : ℝ) ^ C * p.eval (1 / ε)))) ∧
    (Hypothesis_1_6 → ∃ c' : ℝ, 0 < c' ∧ ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
      (¬ ∃ (M : SampleMachine) (K : ℝ) (p : Polynomial ℝ),
          CNFGuarantee M (kParam t r) (dParam r) {ε : ℚ | 0 < ε ∧ ε < 1 / 8}
            (fun n ε => K * (n : ℝ) ^ (c' * kParam t r) * p.eval (1 / ε))) ∧
      (¬ ∃ (M : SampleMachine) (K : ℝ) (p : Polynomial ℝ),
          CNFGuarantee M (kParam t r) (dParam r) {1 / 2 ^ (sParam t r + 4)}
            (fun n ε => K * (n : ℝ) ^ (c' * kParam t r) * p.eval (1 / ε)))) := by sorry

end CNFLearnMQ.Supplement
