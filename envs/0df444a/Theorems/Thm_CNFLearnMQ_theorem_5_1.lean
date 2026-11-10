-- Prove2me | Theorems.Thm_CNFLearnMQ_theorem_5_1
-- name    : CNFLearnMQ.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:17:29.397199+00:00
-- url     : https://prove2.me/theorems/efd8a90c-5a57-4aee-b0de-0ea06e0c9205
-- title:
--   Theorem 5.1 — LearnCNF learns $(k,d)$-CNFs to TV $\varepsilon$ in time $\widetilde O(n^{3+\Xi(t)}+n^{2+2\Xi(t)}/\varepsilon)$
-- statement:
--   Fix a real $t\ge1$ and integers $k\ge100$, $d\ge1$ satisfying the local lemma condition
--   $$k\ge\Big(1+\frac1t\Big)\log d+2\log k+t-3\log t+5.\tag{3}$$
--   There are constants $C>0$ and $a$, depending only on $k,d,t$, such that for every $n\ge k$, every $\varepsilon,\delta\in(0,1)$ and every $n$-variable $(k,d)$-CNF formula $\Phi$: $\Phi$ is satisfiable, and the algorithm LearnCNF$(\varepsilon,\delta)$, given sample access to $\mu_\Phi$ and membership-query access to $\Phi$,
--
--   1. returns a satisfiable formula $\widehat\Phi$ with $d_{\mathrm{TV}}(\mu_\Phi,\mu_{\widehat\Phi})\le\varepsilon$ with probability at least $1-\delta$;
--   2. always runs in time at most
--   $$C\Big(n^{3+\Xi(t)}+\frac{n^{2+2\Xi(t)}}{\varepsilon}\Big)\Big(\ln\frac n\varepsilon\Big)^{2k}\Big(\ln\frac n\delta\Big)^2;$$
--   3. always draws at most $C\,\dfrac{n^{1+\Xi(t)}}{\varepsilon}\big(\ln\frac n\varepsilon+\ln\frac n\delta\big)^a$ samples;
--   4. always asks at most $C\,n^{2+\Xi(t)}\big(\ln\frac n\varepsilon+\ln\frac n\delta\big)^a$ membership queries.
--
--   Here $\log$ is base 2, $\ln$ natural, and $\Xi(t)=\lceil\frac{t-1}{t}\cdot\frac1{G(1/t)}\rceil$ with $G$ the inverse of the binary entropy on $[0,1/2]$; $\Xi(1)=0$. The exponent of $n$ depends only on $t$, not on $k$ or $d$, in contrast with the $n^k$ time of Valiant's clause-elimination learner.
--
--   Differences from the source:
--   - reading: there is an algorithm → the paper's algorithm LearnCNF (Algorithm 3), with the choices the paper leaves arbitrary fixed, written as an oracle program that receives only $n,k,d,t,\varepsilon,\delta$; reason: exhibiting the paper's own algorithm witnesses the existence claim; an existential over programs would make the time clause vacuous because pure code between oracle calls is free
--   - encoding: time $O_{k,d,t}(\cdot)$; sample and query complexity $\widetilde O_{k,d,t}(\cdot)$ → $C$ and the polylog exponent $a$ chosen from $k,d,t$ before $n,\varepsilon,\delta,\Phi$; bounds on every outcome of positive probability; time is the unit-cost charge of `run` and of the algorithms' definitions; reason: the paper's bounds are worst case (it truncates at $N_{\mathrm{tot}}$ to guarantee the running time in the worst case, p.24) and its accounting is unit cost (p.36); $\widetilde O$ suppresses factors logarithmic in $n,1/\varepsilon,1/\delta$, all bounded by powers of $\ln(n/\varepsilon)+\ln(n/\delta)$
--   - encoding: $n=|V|\ge k$ (standing assumption, p.13); $\mu_\Phi$ requires a satisfiable $\Phi$ → hypothesis $k\le n$; satisfiability is part of the conclusion (`∃ h`); reason: the paper's standing assumption; satisfiability follows from (3) via Theorem 3.1 and is proved, not assumed
--   - encoding: $d_{\mathrm{TV}}$ → the published `HybridXorLift.tvDist`, half the $\ell_1$ distance of the two mass functions; reason: the standard total variation distance on a finite set
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Theorem 5.1, p.20

import Mathlib
import Definitions.Def_CNFLearnMQ_Success

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant

/-- Theorem 5.1, p.20 (Feng, Yu, Zhang, *Learning CNF Formulas with Uniform Random Solutions and Membership Queries*, STOC 2027 submission (manuscript sha256 519ee6d4…)). Fix a real `t ≥ 1` and integers `k ≥ 100`, `d ≥ 1` satisfying the
local lemma condition (3), `k ≥ (1 + 1/t) log d + 2 log k + t − 3 log t + 5`. There are constants
`C > 0` and `a`, depending only on `k, d, t`, such that for every `n ≥ k`, every `ε, δ ∈ (0, 1)`
and every `n`-variable `(k, d)`-CNF formula `Φ`: `Φ` is satisfiable, and LearnCNF(ε, δ)
(Algorithm 3), run with sample access to `µ_Φ` and membership-query access to `Φ`,
1. returns a satisfiable formula `Φ̂` with `d_TV(µ_Φ, µ_Φ̂) ≤ ε` with probability at least `1 − δ`;
2. always runs in time at most `C·(n^{3+Ξ(t)} + n^{2+2Ξ(t)}/ε)·(ln(n/ε))^{2k}·(ln(n/δ))²`;
3. always draws at most `C·(n^{1+Ξ(t)}/ε)·(ln(n/ε) + ln(n/δ))^a` samples;
4. always asks at most `C·n^{2+Ξ(t)}·(ln(n/ε) + ln(n/δ))^a` membership queries.

**Formalization Note** The paper's "there is an algorithm" is witnessed by the paper's own algorithm,
`learnCNF`, which receives only `n, k, d, t, ε, δ` and reaches `Φ` only through `run`'s sample and
query answers. Time is the unit-cost charge of `run` and of the definitions (`tick`); "always" means
every outcome of positive probability (worst case; the paper truncates at `N_tot` "to guarantee the
running time in the worst case", p.24). `O_{k,d,t}` and `Õ_{k,d,t}` are read with `C` (and the
polylogarithmic exponent `a`) chosen from `k, d, t` before `n, ε, δ, Φ`. `Ξ(t)` is the natural
number `Xi t`. `log` is base 2 and `ln` natural, as in the paper (p.13). -/
theorem theorem_5_1 (t : ℝ) (k d : ℕ) (ht : 1 ≤ t) (hk : 100 ≤ k) (hd : 1 ≤ d)
    (hLLL : LLLCondition k d t) :
    ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∀ n : ℕ, k ≤ n → ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∀ Φ : CNF n, KD Φ k d → ∃ h : (solutions Φ).Nonempty,
        ENNReal.ofReal (1 - δ) ≤
          prob (run (solutionPMF Φ h) (memOracle Φ) (learnCNF n k d t ε δ))
            (fun o => Success Φ h ε o.1) ∧
        (∀ o ∈ (run (solutionPMF Φ h) (memOracle Φ) (learnCNF n k d t ε δ)).support,
          (o.2.time : ℝ) ≤ C * (((n : ℝ) ^ (3 + Xi t) + (n : ℝ) ^ (2 + 2 * Xi t) / ε) *
            Real.log ((n : ℝ) / ε) ^ (2 * k) * Real.log ((n : ℝ) / δ) ^ 2)) ∧
        (∀ o ∈ (run (solutionPMF Φ h) (memOracle Φ) (learnCNF n k d t ε δ)).support,
          (o.2.samples : ℝ) ≤ C * ((n : ℝ) ^ (1 + Xi t) / ε) *
            (Real.log ((n : ℝ) / ε) + Real.log ((n : ℝ) / δ)) ^ a) ∧
        (∀ o ∈ (run (solutionPMF Φ h) (memOracle Φ) (learnCNF n k d t ε δ)).support,
          (o.2.queries : ℝ) ≤ C * (n : ℝ) ^ (2 + Xi t) *
            (Real.log ((n : ℝ) / ε) + Real.log ((n : ℝ) / δ)) ^ a) := by sorry

end CNFLearnMQ
