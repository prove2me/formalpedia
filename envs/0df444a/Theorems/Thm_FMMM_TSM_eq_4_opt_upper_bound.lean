-- Prove2me | Theorems.Thm_FMMM_TSM_eq_4_opt_upper_bound
-- name    : FMMM.TSM.eq_4_opt_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:27:41.667509+00:00
-- url     : https://prove2.me/theorems/c39ac69e-cce3-4c0a-8f52-2900efff7736
-- title:
--   Eq. (4): high-probability upper bound on OPT
-- statement:
--   Throughout §4.2 until the final proof of Theorem 5 the paper assumes $e_i = 1$ for every impression type: there are $n = |J|$ impression types and $n$ impressions are drawn i.i.d. uniformly from them.
--
--   For every $\varepsilon > 0$ there are constants $C, \delta > 0$ such that for every instance, every maximum 2-matching $F = E_f$ of $E$ and every TSM colouring of $F$:
--
--   1. with probability at least $1 - Ce^{-\delta n}$,
--   $$\mathrm{OPT} \le \tfrac12|E_f| + \left(\tfrac12 - \tfrac1e\right)|E_\delta| + \varepsilon n;$$
--   2. $\tfrac12 |E_f| = |A_{BR}| + |A_{BB}| + \tfrac12(|A_B| + |A_R|)$.
--
--   Together these give equation (4), $\mathrm{OPT} \le |A_{BR}| + |A_{BB}| + \frac12(|A_B| + |A_R|) + (\frac12 - \frac1e)|E_\delta| + \varepsilon n$, the upper half of the ratio analysis.
--
--   Differences from the source:
--   - reading: "with high probability" / "with probability 1 − e^{−Ω(n)}" → failure probability ≤ C·exp(−δn) with C, δ > 0 depending only on ε, uniformly over all instances and all admissible offline choices (maximum 2-matching F and TSM colouring); reason: the paper's asymptotic notation, made explicit; C absorbs small n
--   - encoding: the instance with e_i = 1 for all i (standing assumption of §4.2 until the final proof), draws i.i.d. uniform on I, n = |I| = m → impression types J with n = Fintype.card J and arrivals ω : Fin n → J uniform; reason: the standing assumption of the section, written into the types; same instances
--   - encoding: integral maximum s–t flow of the boosted flow graph G_f (capacities 2, 1, 2) with unit-flow edge set E_f → a maximum 2-matching F of E (IsMaxTwoMatching E F), with E_f = F; reason: integral flows of G_f are exactly the subgraphs of E with all degrees ≤ 2 and the flow value is the number of edges; same objects
--   - encoding: the four colouring rules of §4.2.1 applied to the paths and cycles of E_f → IsTSMColoring F blue: an explicit decomposition of F into vertex-disjoint pieces (whole paths, cycles), each coloured by the rule of its type, with the starting point and orientation of each piece existential; red = F \ blue; reason: the existential orientation is exactly the freedom left by "alternating"; same set of colourings
--   - encoding: n i.i.d. uniform draws (balls into bins) → the counting probability unifProb on sequences Fin n → Ω, draws indexed 0, …, n − 1; reason: the uniform measure on Ωⁿ is the law of n i.i.d. uniform draws; same probabilities
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.3, p. 8, eq. (4)

import Mathlib
import Definitions.Def_FMMM_TSM_unifProb
import Definitions.Def_FMMM_TSM_IsMaxTwoMatching
import Definitions.Def_FMMM_TSM_IsTSMColoring
import Definitions.Def_FMMM_TSM_realOPT
import Definitions.Def_FMMM_TSM_adsWith
import Definitions.Def_FMMM_TSM_eDelta

namespace FMMM.TSM

/-- **Equation (4): high-probability upper bound on OPT.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.3, p. 8, eq. (4): "Summarizing the previous arguments, we get, for any ε > 0, with
probability 1 − e^{−Ω(n)}, OPT ≤ |I_S| + |A_T| + (1 − 1/e)|E_δ| + εn. Applying Equations (3) then
(1), we get OPT ≤ (1/2)|E_f| + (1/2 − 1/e)|E_δ| + εn = |A_BR| + |A_BB| + (1/2)(|A_B| + |A_R|) +
(1/2 − 1/e)|E_δ| + εn".

Unit instance (`n = |J|` uniform draws). For every `ε > 0` there are `C, δ > 0` such that for every
instance, every maximum 2-matching `F` and every TSM colouring `blue`:
1. `Pr[OPT > (1/2)|F| + (1/2 − 1/e)|E_δ| + εn] ≤ C e^{−δn}`;
2. `(1/2)|F| = |A_BR| + |A_BB| + (1/2)(|A_B| + |A_R|)`.

**Formalization Note.** "With probability `1 − e^{−Ω(n)}`" is read as failure probability
`≤ C e^{−δn}` with `C, δ` depending only on `ε`, uniformly over instances and admissible runs. -/
theorem eq_4_opt_upper_bound :
    ∀ ε : ℝ, 0 < ε → ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (A J : Type) [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
        (E F blue : Finset (A × J)), IsMaxTwoMatching E F → IsTSMColoring F blue →
        unifProb J (Fintype.card J) (fun ω =>
            (1 / 2 : ℝ) * F.card + (1 / 2 - 1 / Real.exp 1) * (eDelta E F).card +
              ε * Fintype.card J < (realOPT E ω : ℝ))
          ≤ C * Real.exp (-(δ * Fintype.card J)) ∧
        (1 / 2 : ℝ) * F.card = (adsWith F blue 1 1).card + (adsWith F blue 2 0).card +
          (1 / 2 : ℝ) * ((adsWith F blue 1 0).card + (adsWith F blue 0 1).card) := by sorry

end FMMM.TSM
