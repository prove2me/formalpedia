-- Prove2me | Theorems.Thm_FMMM_TSM_eq_2_alg_lower_bound
-- name    : FMMM.TSM.eq_2_alg_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:25:16.520787+00:00
-- url     : https://prove2.me/theorems/7f327e21-b6f7-4b9b-a570-16c358cf470f
-- title:
--   Eq. (2): high-probability lower bound on ALG
-- statement:
--   Throughout §4.2 until the final proof of Theorem 5 the paper assumes $e_i = 1$ for every impression type: there are $n = |J|$ impression types and $n$ impressions are drawn i.i.d. uniformly from them.
--
--   For every $\varepsilon > 0$ there are constants $C, \delta > 0$ such that for every instance, every maximum 2-matching $F$ of $E$ (the integral max flow of $G_f$) and every TSM colouring of $F$, with probability at least $1 - Ce^{-\delta n}$ both
--
--   $$\mathrm{ALG} \ge \left(1 - \frac{1}{e^2}\right)|A_{BB}| + \left(1 - \frac{2}{e^2}\right)|A_{BR}| + \left(1 - \frac1e\right)|A_B| + \left(1 - \frac2e\right)|A_R| - 4\varepsilon n$$
--
--   and
--
--   $$\mathrm{ALG} \ge \left(1 - \frac{1}{e^2}\right)|A_{BB}| + \left(1 - \frac{2}{e^2}\right)|A_{BR}| + \left(1 - \frac{3}{2e}\right)(|A_B| + |A_R|) - 4\varepsilon n. \qquad (2)$$
--
--   Here $\mathrm{ALG}$ is the number of ads assigned by the online phase. This is the lower half of the ratio analysis.
--
--   Differences from the source:
--   - reading: "with high probability" / "with probability 1 − e^{−Ω(n)}" → failure probability ≤ C·exp(−δn) with C, δ > 0 depending only on ε, uniformly over all instances and all admissible offline choices (maximum 2-matching F and TSM colouring); reason: the paper's asymptotic notation, made explicit; C absorbs small n
--   - encoding: the instance with e_i = 1 for all i (standing assumption of §4.2 until the final proof), draws i.i.d. uniform on I, n = |I| = m → impression types J with n = Fintype.card J and arrivals ω : Fin n → J uniform; reason: the standing assumption of the section, written into the types; same instances
--   - encoding: integral maximum s–t flow of the boosted flow graph G_f (capacities 2, 1, 2) with unit-flow edge set E_f → a maximum 2-matching F of E (IsMaxTwoMatching E F), with E_f = F; reason: integral flows of G_f are exactly the subgraphs of E with all degrees ≤ 2 and the flow value is the number of edges; same objects
--   - encoding: the four colouring rules of §4.2.1 applied to the paths and cycles of E_f → IsTSMColoring F blue: an explicit decomposition of F into vertex-disjoint pieces (whole paths, cycles), each coloured by the rule of its type, with the starting point and orientation of each piece existential; red = F \ blue; reason: the existential orientation is exactly the freedom left by "alternating"; same set of colourings
--   - encoding: n i.i.d. uniform draws (balls into bins) → the counting probability unifProb on sequences Fin n → Ω, draws indexed 0, …, n − 1; reason: the uniform measure on Ωⁿ is the law of n i.i.d. uniform draws; same probabilities
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.2, p. 7, eq. (2) and the display before it

import Mathlib
import Definitions.Def_FMMM_TSM_unifProb
import Definitions.Def_FMMM_TSM_IsMaxTwoMatching
import Definitions.Def_FMMM_TSM_IsTSMColoring
import Definitions.Def_FMMM_TSM_tsmRun
import Definitions.Def_FMMM_TSM_adsWith

namespace FMMM.TSM

/-- **Equation (2): high-probability lower bound on ALG.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.2, p. 7: "We may conclude that with high probability (over the scenarios),
ALG ≥ (1 − 1/e²)|A_BB| + (1 − 2/e²)|A_BR| + (1 − 1/e)|A_B| + (1 − 2/e)|A_R| − 4εn. Note that since
|A_B| ≥ |A_R|, we can also assert ALG ≥ (1 − 1/e²)A_BB + (1 − 2/e²)A_BR + (1 − 3/(2e))(A_B + A_R)
− 4εn. (2)"

Unit instance (`e_i = 1`): ads `A`, impression types `J`, `n = |J|` uniform draws. For every
`ε > 0` there are `C, δ > 0` such that for every instance, every maximum 2-matching `F` (integral
max flow) and every TSM colouring `blue`, the probability that ALG falls below either displayed
bound is at most `C e^{−δn}`.

**Formalization Note.** "With high probability" is read as failure probability `≤ C e^{−δn}` with
`C, δ` depending only on `ε`, uniformly over instances and admissible runs (`C` absorbs small
`n`). ALG is the number of assigned ads of `tsmRun`. -/
theorem eq_2_alg_lower_bound :
    ∀ ε : ℝ, 0 < ε → ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (A J : Type) [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
        (E F blue : Finset (A × J)), IsMaxTwoMatching E F → IsTSMColoring F blue →
        unifProb J (Fintype.card J) (fun ω =>
          ((tsmRun blue (F \ blue) ω).card : ℝ) <
              (1 - 1 / Real.exp 2) * (adsWith F blue 2 0).card +
                (1 - 2 / Real.exp 2) * (adsWith F blue 1 1).card +
                (1 - 1 / Real.exp 1) * (adsWith F blue 1 0).card +
                (1 - 2 / Real.exp 1) * (adsWith F blue 0 1).card - 4 * ε * Fintype.card J ∨
          ((tsmRun blue (F \ blue) ω).card : ℝ) <
              (1 - 1 / Real.exp 2) * (adsWith F blue 2 0).card +
                (1 - 2 / Real.exp 2) * (adsWith F blue 1 1).card +
                (1 - 3 / (2 * Real.exp 1)) *
                  ((adsWith F blue 1 0).card + (adsWith F blue 0 1).card) -
                4 * ε * Fintype.card J)
          ≤ C * Real.exp (-(δ * Fintype.card J)) := by sorry

end FMMM.TSM
