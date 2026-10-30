-- Prove2me | Theorems.Thm_FMMM_TSM_tight_alg_opt
-- name    : FMMM.TSM.tight_alg_opt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:32:01.164669+00:00
-- url     : https://prove2.me/theorems/1c18772b-31ce-4c8a-8e0b-56fee0c6b4a5
-- title:
--   §4.2.5, p. 10: ALG and OPT on the tight family
-- statement:
--   Consider the tight family with parameter $m \ge 1$: $n = 4m$ ads, $n$ impression types and $n$ arrivals drawn uniformly from the types, with the 6-cycle flow. For every $\varepsilon > 0$ there are constants $C, \delta > 0$ such that for every $m \ge 1$ and every TSM colouring of the 6-cycles, with probability at least $1 - Ce^{-\delta n}$,
--
--   $$\left|\mathrm{ALG} - \frac{3n}{4}\left(1 - \frac{2}{e^2}\right)\right| \le \varepsilon n \qquad\text{and}\qquad \mathrm{OPT} \ge n\left(1 - \frac{1}{2e}\right) - \varepsilon n.$$
--
--   Hence the ratio $\mathrm{ALG}/\mathrm{OPT}$ concentrates at most around $\frac{(3/4)(1 - 2/e^2)}{1 - 1/(2e)} = \alpha$: the algorithm cannot achieve a factor better than $\alpha$ on this family.
--
--   Differences from the source:
--   - reading: "with high probability" / "with probability 1 − e^{−Ω(n)}" → failure probability ≤ C·exp(−δn) with C, δ > 0 depending only on ε, uniformly over all instances and all admissible offline choices (maximum 2-matching F and TSM colouring); reason: the paper's asymptotic notation, made explicit; C absorbs small n
--   - reading: "the algorithm achieves the total matching size of (3n/4)(1 − 2/e²) with high probability" → |ALG − (3n/4)(1 − 2/e²)| ≤ εn with high probability; reason: the paper's approximate equality made explicit with the usual εn slack
--   - generalization: the run of the algorithm (its colouring of the 6-cycles) → every TSM colouring of the 6-cycles; reason: every alternating colouring makes each cycle ad an A_BR ad, so the claim holds for all of them; it specializes to the algorithm's run
--   - encoding: i ∈ [1, n/4] → Fin m, 0-based, with m ≥ 1 and n = 4m; reason: same family
--   - encoding: the four colouring rules of §4.2.1 applied to the paths and cycles of E_f → IsTSMColoring F blue: an explicit decomposition of F into vertex-disjoint pieces (whole paths, cycles), each coloured by the rule of its type, with the starting point and orientation of each piece existential; red = F \ blue; reason: the existential orientation is exactly the freedom left by "alternating"; same set of colourings
--   - encoding: n i.i.d. uniform draws (balls into bins) → the counting probability unifProb on sequences Fin n → Ω, draws indexed 0, …, n − 1; reason: the uniform measure on Ωⁿ is the law of n i.i.d. uniform draws; same probabilities
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.5, p. 10

import Mathlib
import Definitions.Def_FMMM_TSM_unifProb
import Definitions.Def_FMMM_TSM_IsTSMColoring
import Definitions.Def_FMMM_TSM_tsmRun
import Definitions.Def_FMMM_TSM_realOPT
import Definitions.Def_FMMM_TSM_tightFlow
import Definitions.Def_FMMM_TSM_tightE

namespace FMMM.TSM

/-- **ALG and OPT on the tight family.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.5, p. 10: "Using Fact 1, one can easily check that the algorithm achieves the total
matching size of (3n/4)(1 − 2/e²) with high probability. The following assignment can be made with
high probability, and is a lower bound on OPT. … Thus, this assignment has size
n/4 + n/4 + (1 − 1/e)(n/2) = n(1 − 1/(2e))."

Tight family with `m ≥ 1`, `n = 4m` uniform draws over the `4m` types, flow `tightFlow m`. For
every `ε > 0` there are `C, δ > 0` such that for every `m ≥ 1` and every TSM colouring `blue` of
the 6-cycles, with probability at least `1 − C e^{−δn}`:
`|ALG − (3n/4)(1 − 2/e²)| ≤ εn` and `OPT ≥ n(1 − 1/(2e)) − εn`.

**Formalization Note.** "With high probability" is read as failure probability `≤ C e^{−δn}` with
`C, δ` depending only on `ε`. "Achieves the total matching size of (3n/4)(1 − 2/e²)" is read as
`ALG` within `εn` of that value; the statement holds for every TSM colouring of the 6-cycles. -/
theorem tight_alg_opt :
    ∀ ε : ℝ, 0 < ε → ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ m : ℕ, 1 ≤ m → ∀ blue : Finset ((Fin 4 × Fin m) × (Fin 4 × Fin m)),
        IsTSMColoring (tightFlow m) blue →
        unifProb (Fin 4 × Fin m) (Fintype.card (Fin 4 × Fin m)) (fun ω =>
            ¬ (|((tsmRun blue (tightFlow m \ blue) ω).card : ℝ) -
                  3 * (4 * m : ℝ) / 4 * (1 - 2 / Real.exp 2)| ≤ ε * (4 * m : ℝ) ∧
                (4 * m : ℝ) * (1 - 1 / (2 * Real.exp 1)) - ε * (4 * m : ℝ) ≤
                  (realOPT (tightE m) ω : ℝ)))
          ≤ C * Real.exp (-(δ * (4 * m : ℝ))) := by sorry

end FMMM.TSM
