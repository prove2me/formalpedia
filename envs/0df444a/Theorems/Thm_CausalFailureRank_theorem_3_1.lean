-- Prove2me | Theorems.Thm_CausalFailureRank_theorem_3_1
-- name    : CausalFailureRank.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:16:09.23024+00:00
-- url     : https://prove2.me/theorems/8bcb7808-4379-47e0-a648-f22458afcacb
-- title:
--   Theorem 3.1 — fixed-graph price law $V_I(\delta)=C(1,U)\ell_d(1/\delta)(1+o(1))$
-- statement:
--   Fix an instance: graph, stage order, priors, channels, observation prices and correction fees. Let $V_I(\delta)$ be the infimum, over all lawful randomized visible-history policies with failure probability at most $\delta$, of the expected actual observation and correction charges.
--
--   1. If $d=\rho(1,U)<\infty$ then $C(1,U)>0$, and as $\delta\to0$, for caps satisfying the certificate of App. B.5,
--   $$V_I(\delta)=C(1,U)\,\ell_d(1/\delta)\,(1+o(1)).$$
--   The lower bound holds for all caps, including none; the upper bound is uniform over qualifying caps.
--   2. For any initial remaining set $R$ of finite rank $d$,
--   $$C(1,R)=\sum_{i=1}^NA_i\,\mathbf 1\{b_i=d-1\},$$
--   with $b_i=0$ if $S_i\cap R=\emptyset$ and $b_i=\max_{r\in S_i\cap R}\rho(i+1,R\setminus\{r\})$ otherwise.
--   3. If the initial rank is infinite, zero observations suffice and the actual correction bill remains bounded by $\min(N,q)f_{\max}$.
--
--   The law is pointwise in the instance. The rank of a combinatorial allocation game thus determines the depth of the iterated logarithm in the statistical price of reliability.
--
--   Differences from the source:
--   - generalization: rational probabilities, fees and risk parameters → real ones; reason: rationality serves only computability, which is not claimed here; the rational case is an instance
--   - generalization: one value $V_I$ → both $V$ with delayed execution and $V$ with immediate execution: the lower bound on the larger class, the upper bound on the smaller, the asymptotic for each; reason: §2 allows both readings of contract I; neither is lost
--   - generalization: limits satisfying App. B.5 in the infinite-rank clause → $H\ge H_0+\min(N,q)$ and any quotas; reason: implied by (25); the policy buys no reviews
--   - reading: "the given limits may vary" as $\delta\to0$ → uniform over caps in the lower and upper bounds, and the literal family form of (3); reason: equivalent to the statement for every family of caps
--   - reading: "integers $\bar M_i\ge M_i$ and $\bar L_i\ge L_i$ are obtained by comparing …" → existentially quantified in the certificate; reason: the source names no unique integers; every printed choice qualifies
--   - encoding: $H_0$ bounds the normal calls → $H_0$ is the sum of a per-stage count of normal calls charged at the write; reason: §2 fixes no count; all zero recovers a bound on reviews and corrections
--   - encoding: stages $1,\dots,N+1$; $b_i=d-1$ → 0-based stages; $b_i+1=d$ in the extended naturals; reason: no truncated subtraction
--   - encoding: rank via an adaptive error adversary → existence of a causal allocator handling all patterns; reason: for a pure causal strategy the adversary can simulate it
--   - generalization: "zero observations suffice and the actual correction bill remains bounded" → a deterministic policy with no observation event, success on every sample and an actual correction bill at most $\min(N,q)f_{\max}$ on every sample; reason: B.4 rule 1 and §2 ("Every policy uses at most min(N, q) genuine corrections") give it; the explicit bound implies the source’s boundedness, and sure success gives failure probability $0$, so the policy is $\delta$-safe for every $\delta\ge0$
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), §3.1, Theorem 3.1, p.6

import Mathlib
import Definitions.Def_CausalFailureRank_coefficient
import Definitions.Def_CausalFailureRank_V
import Definitions.Def_CausalFailureRank_Qualifies

open Filter Topology MeasureTheory

namespace CausalFailureRank

variable {N q : ℕ}

open scoped Classical in
/-- **Theorem 3.1 (Fixed-graph price law).** Zang, Li, Jin, Xu, *Causal Failure Rank Determines Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), §3.1, p.6: "Under early reports and contract I, with
the freshness, correction, and charging rules of Section 2, suppose the given sampling and call limits
satisfy the explicit sufficient bounds in Section B.5. If d = ρ(1, U) < ∞, the infimum V_I(δ) of expected
actual observation and correction charges satisfies V_I(δ) = C(1, U) ℓ_d(1/δ)(1 + o(1)), C(1, U) > 0.
(3) For any fixed initial remaining set R of finite rank d, its coefficient has the ordered expression
C(1, R) = Σ_{i=1}^N A_i 1{b_i = d − 1}, … (4) If the initial rank is infinite, zero observations suffice
and the actual correction bill remains bounded. The asymptotic statement is pointwise for each fixed
graph and channel instance. The lower bound holds regardless of those resource bounds."

**Formalization Note.** Pointwise: the threshold in `∀ᶠ δ` follows the instance and `ε`, and is uniform
over caps, since "the given sampling and call limits may vary" as `δ → 0`; the last conjunct of the first
clause is (3) literally, for every family of caps. The lower bound is on the larger class (`current`, delayed
execution) and for all caps, including none; the upper bound is on the smaller class (`currentPay`). Stage
`1` is `0`. `V` is valued in `ℝ≥0∞`, and `toReal` is taken only under the certificate, where it is finite. -/
theorem theorem_3_1 (I : Instance N q) :
    (∀ d : ℕ, rank I 0 Finset.univ = d →
      0 < C I 0 Finset.univ ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ caps : Caps N,
        ENNReal.ofReal ((1 - ε) * C I 0 Finset.univ * iterLog d (1 / δ)) ≤ V I .current caps δ) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ caps : Caps N, Qualifies I caps δ →
        V I .currentPay caps δ ≤ ENNReal.ofReal ((1 + ε) * C I 0 Finset.univ * iterLog d (1 / δ))) ∧
      ∀ (κ : Contract) (caps : ℝ → Caps N), (∀ᶠ δ in 𝓝[>] (0 : ℝ), Qualifies I (caps δ) δ) →
        Tendsto (fun δ => (V I κ (caps δ) δ).toReal / (C I 0 Finset.univ * iterLog d (1 / δ)))
          (𝓝[>] 0) (𝓝 1)) ∧
    (∀ (R : Finset (Fin q)) (d : ℕ), rank I 0 R = d →
      C I 0 R = ∑ i : Fin N, if db I i R + 1 = d then A I i else 0) ∧
    (rank I 0 Finset.univ = ⊤ → ∀ caps : Caps N,
      ((∑ i, I.normalCalls i + min N q : ℕ) : ℕ∞) ≤ caps.H →
      ∃ π : History I → Action N q, ∀ ω,
        (∀ n, (runFrom I .currentPay caps π (initState I) ω n).history.countP Event.isObs = 0) ∧
        SuccessFrom I .currentPay caps π (initState I) ω ∧
        billFrom I .currentPay caps π (initState I) ω ≤ ENNReal.ofReal ((min N q : ℕ) * fmax I)) := by sorry

end CausalFailureRank
