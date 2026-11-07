-- Prove2me | Theorems.Thm_FairKMeans_proposition_29
-- name    : FairKMeans.proposition_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:34:44.969354+00:00
-- url     : https://prove2.me/theorems/21ca92cc-d9ab-4e0c-bdbd-3ef8c82a1c47
-- title:
--   Proposition 29, head and part 2 — $1$ $k$-means call, $\le\lceil576/\eta^2\rceil+3$ LPs of size $(n+k+1)^{O(\rho/\epsilon)}$ (corrected: $n\to n+k$ in the LP-size and time bounds)
-- statement:
--   Let $\rho\ge1$, $\varepsilon\in(0,1]$, $\eta=\min\{1/10,\varepsilon/(3\rho)\}$, let the instance have a fair solution, and run Algorithm 1 (candidate sets of Lemma 15, part 2) with exact LP oracles and a $\rho$-approximate weighted $k$-means oracle. Then:
--
--   1. it calls the $k$-means oracle once and solves $N_{LP}=(\text{iterations})+2\le\lceil576/\eta^2\rceil+3\le 57604(\rho/\varepsilon)^2$ linear programs: one for $T_0$, one per iteration, one for $S_\pi$;
--   2. there is an absolute constant $C$ (independent of $\rho,\varepsilon,d,n,m,k$ and the oracles) such that every LP has at most $C(n+k+1)^{\lceil C\rho/\varepsilon\rceil}$ variables and $C(n+m+1)(n+k+1)^{\lceil C\rho/\varepsilon\rceil}$ constraints, the input of the $k$-means call has at most $C(n+1)^{\lceil C\rho/\varepsilon\rceil}$ points, and the number of real-RAM operations outside the LP solver and the $k$-means algorithm is at most $C(d+1)(n+k+1)^{\lceil C\rho/\varepsilon\rceil}$.
--
--   The running time is therefore $N_{LP}\cdot T_{LP}+T_{km}$ plus a polynomial for fixed $\rho,\varepsilon$.
--
--   **Formalization Note** Part 1 of the proposition (fixed dimension, Matoušek's candidate sets) is not formalized.
--
--   Differences from the source:
--   - correction: every LP has n^{O(ρ/ϵ)} variables and (n+m)n^{O(ρ/ϵ)} constraints, k-means input n^{O(ρ/ϵ)} points, time d n^{O(ρ/ϵ)} → (n+k+1) in place of n in the LP and time bounds, (n+1) for the k-means input; reason: the final LP has n·|S_π| variables and the oracle may return k centers; counterexample n = d = m = 1, P^(1) = P, β1 = 0, α1 = 1, k → ∞; the proof's 'k ≤ n' (p.36) is never assumed; the +1 covers n = 1, where (ρ/ϵ)² iterations still occur
--   - encoding: standing assumption (the instance has a fair solution, p.19) and the exact LP solvers of Algorithm 1 → hypotheses HasFairSolution, IsFairLPOracle, IsLP29Oracle; reason: stated once for the whole analysis; they keep every assignment of the loop nonnegative, so the k-means oracle receives nonnegative weights and returns at most k centers
--   - reading: O((ρ/ϵ)²) and n^{O(ρ/ϵ)} → explicit 57604(ρ/ϵ)² and an absolute C with exponent ⌈Cρ/ϵ⌉; reason: the O-constants are absolute
--   - encoding: running time N_LP·T_LP + T_km + d n^{O(ρ/ϵ)} → LP and k-means time separate; operation count arithOps outside the oracles; reason: footnote 1 cost model
--   - encoding: constraint counts 'besides the nonnegativity constraints' (p.36) → counts including nonnegativity constraints; reason: over-counting by n·s only
-- source:
--   Cheng–Mo–Song–Ding, A (3+ε)-Approximation for Fair k-Means and a Matching Lower Bound, arXiv:2609.07974 (held version, sha256 73e9312c…), Proposition 29, head and part 2, p.35 (PDF p.37); proof pp.35–36 (PDF pp.37–38)

import Mathlib
import Definitions.Def_FairKMeans_Model
import Definitions.Def_FairKMeans_WeightedKMeans
import Definitions.Def_FairKMeans_RelaxedSolution
import Definitions.Def_FairKMeans_CandidateSets
import Definitions.Def_FairKMeans_LPOracles
import Definitions.Def_FairKMeans_Algorithm1

namespace FairKMeans

/-- **Proposition 29 (Running time), head and part 2** (corrected: `n → n + k` in the LP-size
and time bounds), p.35 (PDF 37), proof pp.35–36 (PDF 37–38). Cheng–Mo–Song–Ding,
arXiv:2609.07974 (held version, sha256 73e9312c…).

Algorithm 1 calls the k-means algorithm once and solves `N_LP ≤ ⌈576/η²⌉ + 3 = O((ρ/ε)²)`
linear programs: one for `T₀`, one in each iteration of the loop, and one for `S_π`. In
unrestricted dimension (candidate sets of Lemma 15, part 2) there is an absolute constant `C`
such that every LP has at most `C (n+k+1)^{⌈Cρ/ε⌉}` variables and
`C (n+m+1)(n+k+1)^{⌈Cρ/ε⌉}` constraints, the input of the k-means call has at most
`C (n+1)^{⌈Cρ/ε⌉}` points, and the number of real-RAM operations outside the LP solver and the
k-means algorithm is at most `C (d+1)(n+k+1)^{⌈Cρ/ε⌉}` (the running time is
`N_LP·T_LP + T_km` plus this count).

**Formalization Note.** As printed, part 2 bounds the LP sizes by `n^{O(ρ/ε)}`; the final LP has
`n·|S_π|` variables and a ρ-approximate oracle may return `k` centers, so for `k ≫ n` this
fails; `n + k + 1` replaces `n` (the `+1` also covers `n ≤ 1`). The k-means oracle returns at most
`k` centers (`IsRhoApprox`) only on nonnegative weights, so the proposition is stated in the
paper's setting: the instance has a fair solution (p.19) and both LP solvers are exact. Then every
assignment the loop holds is nonnegative, `π(T)` carries nonnegative weights and `|S_π| ≤ k`.
Without these hypotheses the bound fails: a fair-LP oracle returning `−1` everywhere gives
negative weights, on which a ρ-approximate oracle may return any number of centers. -/
theorem proposition_29 :
    ∃ C : ℕ, ∀ (ρ ε : ℝ), 1 ≤ ρ → ε ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ (d n m : ℕ) (I : Instance d n m), HasFairSolution I →
        ∀ (fairLP : FairLPOracle d n) (lp29 : LP29Oracle d n) (KM : KMOracle d),
        IsFairLPOracle I fairLP → IsLP29Oracle I lp29 → IsRhoApprox ρ I.k KM →
        (alg1 ρ ε I fairLP lp29 KM).kmCalls = 1 ∧
        (alg1 ρ ε I fairLP lp29 KM).lpCalls = (alg1 ρ ε I fairLP lp29 KM).iterations + 2 ∧
        (alg1 ρ ε I fairLP lp29 KM).lpSizes.length = (alg1 ρ ε I fairLP lp29 KM).lpCalls ∧
        (alg1 ρ ε I fairLP lp29 KM).lpCalls ≤ ⌈576 / eta ρ ε ^ 2⌉₊ + 3 ∧
        ((alg1 ρ ε I fairLP lp29 KM).lpCalls : ℝ) ≤ 57604 * (ρ / ε) ^ 2 ∧
        (∀ L ∈ (alg1 ρ ε I fairLP lp29 KM).lpSizes,
          L.1 ≤ C * (n + I.k + 1) ^ ⌈(C : ℝ) * ρ / ε⌉₊ ∧
          L.2 ≤ C * (n + m + 1) * (n + I.k + 1) ^ ⌈(C : ℝ) * ρ / ε⌉₊) ∧
        (alg1 ρ ε I fairLP lp29 KM).kmInputSize ≤ C * (n + 1) ^ ⌈(C : ℝ) * ρ / ε⌉₊ ∧
        (alg1 ρ ε I fairLP lp29 KM).arithOps ≤
          C * (d + 1) * (n + I.k + 1) ^ ⌈(C : ℝ) * ρ / ε⌉₊ := by sorry

end FairKMeans
