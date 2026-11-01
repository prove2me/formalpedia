-- Prove2me | Theorems.Thm_BanditExpDesign_variance_proxy_bound
-- name    : BanditExpDesign.variance_proxy_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:44.847966+00:00
-- url     : https://prove2.me/theorems/6d5373ad-8744-4dd6-85f5-b756cb3d8b62
-- title:
--   Proof of Theorem 7, p.ec12 — $V^{(i,j)}_t\le(2C'+1)(t+1)^{1+\alpha}$
-- statement:
--   Let $K\ge2$, $\alpha\in[0,1]$ and $\delta\in(0,2/e)$, and run EXP3EG (Algorithm 2) with these inputs. Along every history, for $i\ne j$ and every round $t\ge1$ of the history,
--   $$V_t^{(i,j)}=\sum_{s=1}^t\Big(\frac1{\pi_s(i)}+\frac1{\pi_s(j)}\Big)\le(2C'+1)(t+1)^{1+\alpha},\qquad C'=K^2(1+e^2).$$
--
--   Forced exploration caps $1/\pi_s(a)$ at $Ks^\alpha$ once an arm is eliminated, and (EC.7) caps it at $C'$ before that, which gives a deterministic bound on a random variance.
--
--   Differences from the source:
--   - reading: V_t^{(i,j)} is not defined on p.ec12 → V_t^{(i,j)} = Σ_{s≤t}(1/π_s(i) + 1/π_s(j)); reason: the proxy named on p.ec10 and p.ec13; by (EC.11) it also bounds the conditional variance, so this is the stronger reading
--   - reading: the chain V_t ≤ … ≤ 2C′t + 2(t+1)^{1+α}/(K(1+α)) ≤ (2C′+1)(t+1)^{1+α} → the endpoint V_t ≤ (2C′+1)(t+1)^{1+α}; reason: the printed middle terms have a slip: an eliminated arm contributes K s^α, not s^α/K; the endpoint is true
--   - reading: R̂^max_t is the maximum over all arms (p.13) → R̂^max_t is the maximum over the active set 𝒜_t; reason: the printed rule can empty 𝒜_t and leave π_t undefined; the proofs of the paper, (EC.9)–(EC.10), use the active-set maximum, and the two rules agree while all arms are active
--   - encoding: ε_0 is used at t = 1 and not defined → ε_0 = 0; reason: R̂_0 = 0, so π_1 = 1/K for every value of ε_0; Algorithm 1 sets the same value
--   - encoding: arms {1, …, K}; natural log written log or ln; t^α → Fin K; Real.log; Real.rpow; reason: Lean conventions; same instances
-- source:
--   Simchi-Levi–Wang, Multi-armed Bandit Experimental Design, SSRN 4224969, proof of Theorem 7, line before (EC.12), p.ec12

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_BanditPolicy
import Definitions.Def_BanditExpDesign_EXP3EG

set_option autoImplicit false
open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace BanditExpDesign

/-- **The variance proxy bound**, Simchi-Levi–Wang, *Multi-armed Bandit Experimental Design*,
SSRN 4224969, proof of Theorem 7, p.ec12: for all `t`,
`V_t^{(i,j)} ≤ (2C' + 1)(t + 1)^{1+α}` with `C' = K²(1+e²)`.

**Formalization Note.** Pathwise. `V_t^{(i,j)}` is the proxy `∑_{s=1}^t (1/π_s(i) + 1/π_s(j))`, which
bounds the conditional variance by (EC.11). The printed middle terms carry a slip (`/K` for
`K`) and are not part of the statement. -/
theorem variance_proxy_bound {K : ℕ} [NeZero K] (hK : 2 ≤ K) {α δ : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) (hδ0 : 0 < δ) (hδ : δ < 2 / Real.exp 1) {n : ℕ}
    (h : BanditHistory K n) (i j : Fin K) (hij : i ≠ j) (t : ℕ) (ht1 : 1 ≤ t) (htn : t ≤ n) :
    varianceProxy α δ h t i j ≤ (2 * constC' K + 1) * ((t : ℝ) + 1) ^ (1 + α) := by sorry

end BanditExpDesign
