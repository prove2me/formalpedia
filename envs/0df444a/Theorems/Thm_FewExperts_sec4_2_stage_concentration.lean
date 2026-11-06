-- Prove2me | Theorems.Thm_FewExperts_sec4_2_stage_concentration
-- name    : FewExperts.sec4_2_stage_concentration
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:55:31.391177+00:00
-- url     : https://prove2.me/theorems/e2f51052-0241-482d-a2a1-4040c8d026ba
-- title:
--   §4.2, p.22 — w.p. $1-\frac1{4T}$ the potential stays $\ge L/2$ at the ends of runs and exceeds $2L$ after $2^9rs/\alpha$ stopped runs
-- statement:
--   For all sufficiently large $N$ and $T$ with $L_0<T$ (the standing assumption of §4.2), and for every gain array, the following holds except with probability at most $1/(4T)$ on the sampling event of p.20.
--
--   1. At the end of every epoch whose HarvestGain run stopped, the potential $S=\mathrm{softmin}_{8s/L}(a)$ at that epoch's scale $L$ is at least $L/2$.
--   2. For every scale $L=2^cL_0$, if all $\lceil2^9rs/\alpha\rceil$ epochs of that scale ran and stopped, the potential at the end of the scale is above $2L$.
--
--   This is the step where Azuma–Hoeffding, applied to the failure indicators of the runs, turns the per-run bounds (18)–(19) into steady growth of the potential.
--
--   Differences from the source:
--   - reading: the concentration event (Azuma–Hoeffding on the failure indicators) has probability ≥ 1 − 1/4T, and on it the potential never drops below L/2 and exceeds 2L → the probability that the sampling event holds and the stated consequence fails is ≤ 1/(4T); reason: the paper does not define the concentration event formally; its stated consequence, on the sampling event the analysis assumes from p.20 on, is what the proof uses, and the paper's claim implies this statement
--   - encoding: floors and ceilings omitted (p.13): 1/α levels, m = 4r/q, 2r scales, 2⁹rs/α epochs → K = ⌊1/α⌋ levels (exponent 1/α − j read as K − j), m = ⌈4r/q⌉, ⌈2r⌉ scales, ⌈2⁹rs/α⌉ epochs per scale; reason: the paper omits them where they do not materially affect the analysis; the floor keeps the top threshold Kαℓ ≤ ℓ, which Proposition 2 (i) uses
--   - encoding: T and N sufficiently large (convention of §3, p.13, for everything outside §3) → ∃ N₀ T₀, ∀ N ≥ N₀, ∀ T ≥ T₀; reason: the paper's own convention made explicit
--   - encoding: Pr[bad event] ≤ β → the (outer) measure of the bad event is ≤ ENNReal.ofReal β; reason: equal for measurable events; no measurability statement is needed
-- source:
--   Asi, Feldman, Kale, Koren, Singhal, Talwar, A Few Experts Suffice: Near-Optimal (Private) Online Learning with Limited Subscriptions (manuscript, STOC 2027 submission, sha256 6f26c545886ca169ae416f4056c22bc260e33c3a4fc5d5d8cabe21b5d45398ee), §4.2, p.22 (PDF p.23), with footnote 4

import Mathlib
import Definitions.Def_FewExperts_fewExpertsAlg

namespace FewExperts

open MeasureTheory

/-- **§4.2 stage concentration: the potential stays `≥ L/2` and reaches `2L`.**
Asi, Feldman, Kale, Koren, Singhal, Talwar, *A Few Experts Suffice* (manuscript, sha256
6f26c545…), §4.2, p.22 (PDF 23), with footnote 4: "applying Azuma–Hoeffding (Lemma 1) to the
failure indicators, as we repeat this process (each time updating D and resampling I), the value
of S_t will (with high probability) never go below L/2 at the ends of these runs and eventually,
after 2⁹rs/α stopped runs with the same value of L, go above 2L. The concentration event has
probability at least 1 − 1/4T simultaneously for all values of L used by the algorithm."

For `N`, `T` large enough with `L₀ < T` (the standing assumption of §4.2, p.19) and every gain
array, the probability that the sampling event of p.20 (`SampOK`, "We assume henceforth that
this is the case") holds while the conclusion fails is at most `1/(4T)`. The conclusion
(`StageGood`): at the end of every epoch whose HarvestGain run stopped, the potential
`S = softmin_{8s/L}(a)` at that epoch's scale `L` is at least `L/2`; and for every scale
`L = 2^c L₀`, if all `⌈2⁹rs/α⌉` epochs of that scale ran and stopped, the potential at its end is
above `2L`.

**Formalization Note** The paper's concentration event (Azuma–Hoeffding on the failure
indicators) is not named; the statement bounds the probability that its stated consequence fails
on the sampling event, which follows from the paper's claim. A run that never stops ends the game
at round `T` (footnote 4's convention only enters the proof). Epoch counts carry ceilings. -/
theorem sec4_2_stage_concentration :
    ∃ N₀ T₀ : ℕ, ∀ N T : ℕ, N₀ ≤ N → T₀ ≤ T → ∀ [NeZero N], L0 N T < T →
      ∀ g : ℕ → Fin N → ℝ, IsGainSeq T g →
        fewExpertsLaw {ω | SampOK N T ω g ∧ ¬ StageGood N T ω g} ≤ ENNReal.ofReal (1 / (4 * T)) := by sorry

end FewExperts
