-- Prove2me | Theorems.Thm_DataDepProb_Discrete_theorem_1_1
-- name    : DataDepProb.Discrete.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:10:36.14234+00:00
-- url     : https://prove2.me/theorems/576095fc-c843-4474-9fed-930dd5511e04
-- title:
--   Theorem 1.1 — an explicit estimator with mean squared error $O(\min\{1,d^{1/4}\sqrt{\log(1+d/n)/n}\})$ for every query mapping on $[d]$, $\lceil n/\sqrt d\rceil$ evaluations
-- statement:
--   Let $n\ge1$ and $d\ge2$. For every mapping $\mathcal G:[d]^n\to[0,1]^{[d]}$ there is an explicit randomized estimator $\hat p$ such that
--   $$\sup_{D\in\Delta_d}\ E_{S\sim D^n}\Big[\big(\hat p(S)-E_D[\mathcal G(S)]\big)^2\Big]=O\Big(\min\Big\{1,\ \frac{d^{1/4}}{\sqrt n}\sqrt{\log\Big(1+\frac dn\Big)}\Big\}\Big).$$
--   The estimator uses at most $\lceil n/\sqrt d\rceil$ evaluations of $\mathcal G$ and $O((1+n/\sqrt d)(n+d\log^3(nd)))$ time.
--
--   Formally: there are a constant $C>0$ and one admissible program for the randomized real RAM with a $\mathcal G$-evaluation oracle such that for all $n\ge1$, $d\ge2$ and every $\mathcal G$ with values in $[0,1]$: on every input $S\in[d]^n$ and every random tape the run halts within $C(1+n/\sqrt d)(n+d\log^3(nd))$ steps and makes at most $\lceil n/\sqrt d\rceil$ evaluations of $\mathcal G$; and for every $D\in\Delta_d$ the squared error $(\mathrm{out}-E_D[\mathcal G(S)])^2$ is integrable under $D^n\otimes$(tape law) with integral at most $C\min\{1,d^{1/4}\sqrt{\log(1+d/n)}/\sqrt n\}$.
--
--   Learning $D$ gives error $O(d/n)$; this estimator reaches constant error with $\tilde O(\sqrt d)$ samples, for every query rule, while Theorem 1.2 shows $\Omega(\min\{1,\sqrt d/n\})$ is necessary.
--
--   Differences from the source:
--   - reading: "for every mapping $\mathcal G$ there is an explicit randomized estimator" with an evaluation count and a time bound → one program, fixed before $n,d,\mathcal G,D$, on the mission's machine (unit-cost real RAM with integer memory, exp, log, uniform integer draws, and an `evalG` oracle charged $d$ steps), accessing $\mathcal G$ only through `evalG`; reason: "explicit", "evaluations of $\mathcal G$" and "time" are meaningful only for an oracle program; this is the stronger reading.
--   - reading: $O(\cdot)$ → $C\cdot(\cdot)$ with one universal $C>0$, the same for risk and time; reason: §4.1, $O$ hides a universal constant.
--   - reading: time → steps charged on every run (every input $S$ and every tape), not in expectation; evaluations bounded at every moment by `⌈n/√d⌉₊`; reason: worst-case bounds as printed.
--   - reading: $\sup_D E[\cdot]$ → for every $D\in\Delta_d$: integrability of the squared error under `(sampleLaw n D).prod tapeLaw` and the bound on its integral; reason: an expectation presupposes integrability; a Bochner integral of a non-integrable function would be $0$.
--   - encoding: $[d]$, the sample, the output → `Fin d`; $n,d$ in pointer registers $0,1$, $S$ in integer cells $0..n-1$, output in real register $0$ at the first halted state; the estimator's randomness is a tape of independent Uniform$[0,1]$ cells; reason: input/output and randomness conventions.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 2, Theorem 1.1 (restated p. 14; proved p. 16)

import Mathlib
import Definitions.Def_DataDepProb_Discrete_Simplex
import Definitions.Def_DataDepProb_Discrete_Machine

open MeasureTheory

namespace DataDepProb.Discrete

/-- Theorem 1.1 (discrete distributions, p. 2). There are a universal constant `C > 0` and one
explicit randomized estimator — a single program with rational literals for the unit-cost
randomized real RAM with a `𝒢`-evaluation oracle — such that for all `n ≥ 1`, `d ≥ 2` and every
mapping `𝒢 : [d]^n → [0, 1]^[d]`:
* on every input `S ∈ [d]^n` and every random tape the run halts after at most
  `C(1 + n/√d)(n + d log³(nd))` steps and makes at most `⌈n/√d⌉` evaluations of `𝒢`;
* for every `D ∈ ∆_d`, the squared error `(p̂(S) − E_D[𝒢(S)])²` is integrable for
  `S ∼ D^n` and an independent uniform tape, and its expectation is at most
  `C · min{1, (d^{1/4}/√n) √(log(1 + d/n))}`. -/
theorem theorem_1_1 :
    ∃ C : ℝ, 0 < C ∧ ∃ P : Program, Admissible P ∧
      ∀ (n d : ℕ), 1 ≤ n → 2 ≤ d →
      ∀ G : (Fin n → Fin d) → Fin d → ℝ, (∀ s x, 0 ≤ G s x ∧ G s x ≤ 1) →
        (∀ (S : Fin n → Fin d) (ω : Tape),
          HaltsWithin P G ω (estimatorInput S)
              (C * (1 + (n : ℝ) / Real.sqrt d) *
                ((n : ℝ) + d * Real.log ((n : ℝ) * d) ^ 3)) ∧
          EvalsWithin P G ω (estimatorInput S) (⌈(n : ℝ) / Real.sqrt d⌉₊ : ℝ)) ∧
        ∀ D ∈ simplex d,
          Integrable
              (fun p : (Fin n → Fin d) × Tape =>
                (outReal P G p.2 (estimatorInput p.1) - expect D (G p.1)) ^ 2)
              ((sampleLaw n D).prod tapeLaw) ∧
            ∫ p : (Fin n → Fin d) × Tape,
                (outReal P G p.2 (estimatorInput p.1) - expect D (G p.1)) ^ 2
                ∂((sampleLaw n D).prod tapeLaw)
              ≤ C * min 1 ((d : ℝ) ^ ((1 : ℝ) / 4) / Real.sqrt n *
                  Real.sqrt (Real.log (1 + (d : ℝ) / n))) := by sorry

end DataDepProb.Discrete
