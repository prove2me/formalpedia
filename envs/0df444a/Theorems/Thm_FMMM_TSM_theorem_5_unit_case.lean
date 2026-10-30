-- Prove2me | Theorems.Thm_FMMM_TSM_theorem_5_unit_case
-- name    : FMMM.TSM.theorem_5_unit_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:29:52.04315+00:00
-- url     : https://prove2.me/theorems/d54b8eed-c7d1-4b83-86ea-610ced35a177
-- title:
--   Theorem 5 for $e_i = 1$ (corrected: sign of $\varepsilon$)
-- statement:
--   Throughout §4.2 until the final proof of Theorem 5 the paper assumes $e_i = 1$ for every impression type: there are $n = |J|$ impression types and $n$ impressions are drawn i.i.d. uniformly from them.
--
--   For every $\varepsilon > 0$ and every $c > 0$ there are constants $C, \delta > 0$ such that for every instance with $e_i = 1$, every maximum 2-matching $F$ of $E$ (the integral max flow of $G_f$) and every TSM colouring of $F$,
--
--   $$\Pr\big[\mathrm{OPT} \ge cn \ \text{ and } \ \mathrm{ALG} < (\alpha - \varepsilon)\,\mathrm{OPT}\big] \le Ce^{-\delta n}.$$
--
--   That is, as long as $\mathrm{OPT} = \Omega(n)$, with probability $1 - e^{-\Omega(n)}$ the two suggested matchings algorithm satisfies $\mathrm{ALG}/\mathrm{OPT} + \varepsilon \ge \alpha$. This is the core case of Theorem 5; the general case reduces to it by copying impression types.
--
--   Differences from the source:
--   - correction: ALG/OPT − ε ≥ α (Theorem 5 as printed) → ALG ≥ (α − ε)·OPT, i.e. ALG/OPT + ε ≥ α; reason: the printed form is false since ALG ≤ OPT on every scenario: for ε = 1 it requires ALG/OPT ≥ 1 + α; on G = K_{n,n} with e ≡ 1 (OPT = n always) the printed event has probability 0; the proof on p. 9 concludes ALG/OPT + ε ≥ α
--   - reading: "as long as OPT = Ω(n)" → for every c > 0, the failure event is intersected with {OPT ≥ c·n}, OPT the realized optimum; reason: the proof uses a lower bound on the realized OPT to absorb the ε′n terms
--   - reading: "with high probability" / "with probability 1 − e^{−Ω(n)}" → failure probability ≤ C·exp(−δn) with C, δ > 0 depending only on ε and c, uniformly over all instances and all admissible offline choices (maximum 2-matching F and TSM colouring); reason: the paper's asymptotic notation, made explicit; C absorbs small n
--   - reading: "the two suggested matchings algorithm" (a max-flow, made integral, and a colouring by the rules) → every maximum 2-matching F and every TSM colouring of F; reason: the algorithm leaves these choices open; the bound is claimed for its output, whatever the choices
--   - encoding: the instance with e_i = 1 for all i (standing assumption of §4.2 until the final proof), draws i.i.d. uniform on I, n = |I| = m → impression types J with n = Fintype.card J and arrivals ω : Fin n → J uniform; reason: the standing assumption of the section, written into the types; same instances
--   - encoding: integral maximum s–t flow of the boosted flow graph G_f (capacities 2, 1, 2) with unit-flow edge set E_f → a maximum 2-matching F of E (IsMaxTwoMatching E F), with E_f = F; reason: integral flows of G_f are exactly the subgraphs of E with all degrees ≤ 2 and the flow value is the number of edges; same objects
--   - encoding: the four colouring rules of §4.2.1 applied to the paths and cycles of E_f → IsTSMColoring F blue: an explicit decomposition of F into vertex-disjoint pieces (whole paths, cycles), each coloured by the rule of its type, with the starting point and orientation of each piece existential; red = F \ blue; reason: the existential orientation is exactly the freedom left by "alternating"; same set of colourings
--   - encoding: n i.i.d. uniform draws (balls into bins) → the counting probability unifProb on sequences Fin n → Ω, draws indexed 0, …, n − 1; reason: the uniform measure on Ωⁿ is the law of n i.i.d. uniform draws; same probabilities
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.4, p. 9 (proof of Theorem 5, case e_i = 1)

import Mathlib
import Definitions.Def_FMMM_TSM_unifProb
import Definitions.Def_FMMM_TSM_IsMaxTwoMatching
import Definitions.Def_FMMM_TSM_IsTSMColoring
import Definitions.Def_FMMM_TSM_tsmRun
import Definitions.Def_FMMM_TSM_realOPT
import Definitions.Def_FMMM_TSM_alpha

namespace FMMM.TSM

/-- **Theorem 5 for `e_i = 1` (corrected: sign of ε).**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.4, p. 9: "We first prove the approximation ratio for e_i = 1. The bounds in equations (2)
and (4) each hold with probability 1 − e^{−Ω(n)}, and so using a union bound they both hold with
probability 1 − e^{−Ω(n)}. Using Lemma 1 (ignoring the 1/3 in front of the A_R) and Equation (4),
we get OPT ≤ (4/3 − 2/(3e))A_BR + (5/3 − 4/(3e))A_BB + (1 − 1/e)(A_B + A_R) + ε′n. Since
OPT = Ω(n), we can choose ε′ small enough such that when we apply Equation (2) (also using ε′) we
may conclude ALG/OPT + ε ≥ min{…} = α."

Unit instance (ads `A`, types `J`, `n = |J|` uniform draws). For every `ε > 0` and `c > 0` there
are `C, δ > 0` such that for every instance, every maximum 2-matching `F` (integral max flow of
`G_f`) and every TSM colouring `blue`,
`Pr[OPT ≥ cn ∧ ALG < (α − ε)·OPT] ≤ C e^{−δn}`.

**Formalization Note.** Correction: Theorem 5 prints `ALG/OPT − ε ≥ α`, which is false
(`ALG ≤ OPT` always); the proof concludes `ALG/OPT + ε ≥ α`, written `ALG ≥ (α − ε)·OPT`.
"As long as OPT = Ω(n)" is the event `OPT ≥ cn` for an arbitrary `c > 0`; `C, δ` depend only on
`ε, c`. -/
theorem theorem_5_unit_case :
    ∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c → ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (A J : Type) [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
        (E F blue : Finset (A × J)), IsMaxTwoMatching E F → IsTSMColoring F blue →
        unifProb J (Fintype.card J) (fun ω =>
            c * Fintype.card J ≤ (realOPT E ω : ℝ) ∧
              ((tsmRun blue (F \ blue) ω).card : ℝ) < (alpha - ε) * (realOPT E ω : ℝ))
          ≤ C * Real.exp (-(δ * Fintype.card J)) := by sorry

end FMMM.TSM
