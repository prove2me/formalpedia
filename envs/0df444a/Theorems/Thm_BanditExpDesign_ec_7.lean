-- Prove2me | Theorems.Thm_BanditExpDesign_ec_7
-- name    : BanditExpDesign.ec_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T11:36:13.951924+00:00
-- url     : https://prove2.me/theorems/6f4ca861-2be9-44e5-8ebd-bebffe7518b7
-- title:
--   (EC.7) — active arms have $1/\pi_t(a)\le K^2(1+e^2)$
-- statement:
--   Let $K\ge2$, $\alpha\in[0,1]$ and $\delta\in(0,2/e)$, and run EXP3EG (Algorithm 2) with these inputs. Along every history, for every round $t\ge1$ and every active arm $a\in\mathcal A_t$,
--   $$\frac1{\pi_t(a)}\le K^2(1+e^2)=:C'.$$
--
--   The elimination rule keeps the propensities of active arms away from zero; this is what makes the IPW estimates of active arms stable.
--
--   Differences from the source:
--   - generalization: the proof of Theorem 6 runs with δ = 1/(2n²) → every δ ∈ (0, 2/e); reason: 1/(2n²) ≤ 1/2 < 2/e, so this contains the page's case; Theorem 7 uses the fact for this range of δ
--   - generalization: period t ≥ 2 → every t ≥ 1; reason: π_1(a) = 1/K, so t = 1 holds as well
--   - reading: the display chain (EC.7) → its conclusion 1/π_t(a) ≤ C′; reason: the intermediate lines are steps of the proof; the middle one is loose
--   - reading: R̂^max_t is the maximum over all arms (p.13) → R̂^max_t is the maximum over the active set 𝒜_t; reason: the printed rule can empty 𝒜_t and leave π_t undefined; the proofs of the paper, (EC.9)–(EC.10), use the active-set maximum, and the two rules agree while all arms are active
--   - encoding: ε_0 is used at t = 1 and not defined → ε_0 = 0; reason: R̂_0 = 0, so π_1 = 1/K for every value of ε_0; Algorithm 1 sets the same value
--   - encoding: arms {1, …, K}; natural log written log or ln; t^α → Fin K; Real.log; Real.rpow; reason: Lean conventions; same instances
-- source:
--   Simchi-Levi–Wang, Multi-armed Bandit Experimental Design, SSRN 4224969, proof of Theorem 6, eq. (EC.7), p.ec9

import Mathlib
import Definitions.Def_StochasticBandit
import Definitions.Def_BanditPolicy
import Definitions.Def_BanditExpDesign_EXP3EG

set_option autoImplicit false
open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace BanditExpDesign

/-- **(EC.7)**, Simchi-Levi–Wang, *Multi-armed Bandit Experimental Design*, SSRN 4224969,
proof of Theorem 6, p.ec9: along every history, every arm active in round `t` has
`1/π_t(a) ≤ K²(1+e²) = C'`.

**Formalization Note.** Pathwise. `h` holds `n` rounds and `t ≤ n + 1`, so `π_t` and `𝒜_t`
are determined by `h`. The page says `t ≥ 2`; `t = 1` is included (`π_1 = 1/K`). -/
theorem ec_7 {K : ℕ} [NeZero K] (hK : 2 ≤ K) {α δ : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hδ0 : 0 < δ) (hδ : δ < 2 / Real.exp 1) {n : ℕ} (h : BanditHistory K n) (t : ℕ)
    (ht1 : 1 ≤ t) (htn : t ≤ n + 1) (a : Fin K) (ha : a ∈ activeSet α δ h t) :
    1 / propensity α δ h t a ≤ constC' K := by sorry

end BanditExpDesign
