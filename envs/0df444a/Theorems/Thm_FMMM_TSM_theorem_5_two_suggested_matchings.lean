-- Prove2me | Theorems.Thm_FMMM_TSM_theorem_5_two_suggested_matchings
-- name    : FMMM.TSM.theorem_5_two_suggested_matchings
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:32:43.228363+00:00
-- url     : https://prove2.me/theorems/fb24d391-9e2c-4948-810f-041589104250
-- title:
--   Theorem 5 (corrected: sign of $\varepsilon$): the two suggested matchings algorithm achieves $\alpha \approx 0.670$, tightly
-- statement:
--   Let $G = (A, I, E)$ be a bipartite graph of ads $A$ and impression types $I$, with integers $e_i \ge 0$, $n = \sum_i e_i$, and $n$ impressions drawn i.i.d. from $D$, $\Pr[i] = e_i/n$. The **two suggested matchings (TSM) algorithm** computes offline an integral maximum flow $E_f$ of the boosted flow graph (after replacing each type by $e_i$ copies), colours it blue and red by the rules of §4.2.1, and online sends the first arrival of each copy along its blue edge and the second along its red edge. Write $\mathrm{ALG}$ for the number of assigned impressions and $\mathrm{OPT}$ for the maximum matching of the realization graph, and let
--
--   $$\alpha = \frac{1 - \frac{2}{e^2}}{\frac43 - \frac{2}{3e}} \approx 0.67029.$$
--
--   Then:
--
--   1. $\alpha > 1 - \frac1e$.
--   2. For every $\varepsilon > 0$ and every $c > 0$ there are constants $C, \delta > 0$ such that for every instance, every choice of the maximum flow and every colouring obeying the rules,
--   $$\Pr\big[\mathrm{OPT} \ge cn \ \text{ and } \ \mathrm{ALG} < (\alpha - \varepsilon)\,\mathrm{OPT}\big] \le Ce^{-\delta n};$$
--   that is, as long as $\mathrm{OPT} = \Omega(n)$, with probability $1 - e^{-\Omega(n)}$, $\mathrm{ALG}/\mathrm{OPT} + \varepsilon \ge \alpha$.
--   3. The ratio is tight: for every $\varepsilon > 0$, on the family of §4.2.5 with $n = 4m$ and $m$ large enough, the 6-cycle flow is a maximum flow and the expected approximation factor $E[\mathrm{ALG}/\mathrm{OPT}]$ of the algorithm is at most $\alpha + \varepsilon$.
--
--   The theorem shows that knowing the arrival distribution lets an online matching algorithm beat the $1 - 1/e$ barrier that holds in the adversarial model.
--
--   **Formalization Note** The $n$ draws are uniform over the $n$ copies (type $i$ with probability $e_i/n$, then a uniform name among its copies); $\mathrm{OPT}$ is computed on the drawn types. Edge sets, flows and colourings are encoded as in the mission's definitions.
--
--   Differences from the source:
--   - correction: ALG/OPT − ε ≥ α → ALG ≥ (α − ε)·OPT, i.e. ALG/OPT + ε ≥ α; reason: the printed form is false since ALG ≤ OPT on every scenario: for ε = 1 it requires ALG/OPT ≥ 1 + α; on G = K_{n,n} with e ≡ 1 (OPT = n always, so OPT = Ω(n)) the printed event has probability 0 for every n; the proof on p. 9 concludes ALG/OPT + ε ≥ α
--   - reading: "as long as OPT = Ω(n)" → for every c > 0, the failure event is intersected with {OPT ≥ c·n}, OPT the realized optimum; reason: the proof uses a lower bound on the realized OPT to absorb the ε′n terms
--   - reading: "with probability at least 1 − e^{−Ω(n)}" → failure probability ≤ C·exp(−δn) with C, δ > 0 depending only on ε and c, uniformly over all instances (finite A, I, E, every e); reason: the paper's asymptotic notation, made explicit; C absorbs small n
--   - reading: "the two suggested matchings algorithm" (a max-flow, made integral, and a colouring by the rules) → every maximum 2-matching F of the copy graph and every TSM colouring of F; reason: the algorithm leaves these choices open; the bound is claimed for its output, whatever the choices
--   - reading: "there is a family of instances for which the algorithm has expected approximation factor at most α + ε" → the §4.2.5 family with the 6-cycle flow, which is maximum, has E[ALG/OPT] ≤ α + ε for all large m; reason: the paper's family and the flow it says the algorithm finds; expected approximation factor is E[ALG/OPT] (p. 4)
--   - generalization: the algorithm's colouring on the tight family → every TSM colouring of the 6-cycles; reason: every alternating colouring makes each cycle ad an A_BR ad; specializes to the algorithm's run
--   - encoding: types drawn from D and named uniformly among their e_i copies → n draws uniform over Copy e; OPT computed on the types of the draws; ALG the TSM run on the copy graph; reason: same joint law (copy_reduction); OPT′ = OPT
--   - encoding: integral maximum s–t flow of the boosted flow graph G_f (capacities 2, 1, 2) with unit-flow edge set E_f → a maximum 2-matching F of E (IsMaxTwoMatching E F), with E_f = F; reason: integral flows of G_f are exactly the subgraphs of E with all degrees ≤ 2 and the flow value is the number of edges; same objects
--   - encoding: the four colouring rules of §4.2.1 applied to the paths and cycles of E_f → IsTSMColoring F blue: an explicit decomposition of F into vertex-disjoint pieces (whole paths, cycles), each coloured by the rule of its type, with the starting point and orientation of each piece existential; red = F \ blue; reason: the existential orientation is exactly the freedom left by "alternating"; same set of colourings
--   - encoding: E[ALG/OPT] → expRatio, with ALG/OPT read as 0 when OPT = 0; reason: every scenario of the tight family has OPT ≥ 1, so the convention is never used there
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, Theorem 5, p. 6 (proof §4.2.4, p. 9; tightness §4.2.5, pp. 9–10)

import Mathlib
import Definitions.Def_FMMM_TSM_unifProb
import Definitions.Def_FMMM_TSM_IsMaxTwoMatching
import Definitions.Def_FMMM_TSM_IsTSMColoring
import Definitions.Def_FMMM_TSM_tsmRun
import Definitions.Def_FMMM_TSM_realOPT
import Definitions.Def_FMMM_TSM_Copy
import Definitions.Def_FMMM_TSM_copyEdges
import Definitions.Def_FMMM_TSM_alpha
import Definitions.Def_FMMM_TSM_tightFlow
import Definitions.Def_FMMM_TSM_tightE
import Definitions.Def_FMMM_TSM_expRatio

namespace FMMM.TSM

/-- **Theorem 5 (corrected: sign of ε): the two suggested matchings algorithm.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, Theorem 5, p. 6: "For any ε > 0, with probability at least 1 − e^{−Ω(n)}, as long as
OPT = Ω(n), the two suggested matchings algorithm achieves approximation ratio
ALG/OPT − ε ≥ α := (1 − 2/e²)/(4/3 − 2/(3e)) ≈ 0.67029 > 1 − 1/e. Moreover, this ratio is tight;
specifically, there is a family of instances for which the two suggested matchings algorithm has
expected approximation factor at most α + ε." (Proof §4.2.4, p. 9; tightness §4.2.5, pp. 9–10.)

Three clauses:
1. `1 − 1/e < α`.
2. For every `ε > 0` and `c > 0` there are `C, δ > 0` such that for every instance (ads `A`,
   impression types `I`, edges `E`, integers `e_i ≥ 0`, `n = ∑ e_i`), every maximum 2-matching
   `F` of the copy graph (integral max flow of `G_f`) and every TSM colouring `blue` of `F`:
   `Pr[OPT ≥ cn ∧ ALG < (α − ε)·OPT] ≤ C e^{−δn}`. The `n` draws are uniform over the `n`
   copies (type `i` with probability `e_i/n`, named uniformly among its copies); ALG is the number
   of ads assigned by the TSM run on the copies; OPT is the maximum matching of the realization
   graph of the drawn types.
3. For every `ε > 0`, for all large `m`, in the tight family of §4.2.5 (`n = 4m`) the 6-cycle
   flow is a maximum flow and every TSM colouring of it has `E[ALG/OPT] ≤ α + ε`.

**Formalization Note.** Correction: the printed `ALG/OPT − ε ≥ α` is false (`ALG ≤ OPT`, so for
`ε = 1` it would need `ALG/OPT > 1`; on `K_{n,n}` with `e ≡ 1` the event has probability 0); the
proof on p. 9 concludes `ALG/OPT + ε ≥ α`, stated as `ALG ≥ (α − ε)·OPT`. "OPT = Ω(n)" is the
event `OPT ≥ cn`; "1 − e^{−Ω(n)}" is `C e^{−δn}` with `C, δ` depending only on `ε, c`, uniform over
instances and over the offline choices (flow and colouring). -/
theorem theorem_5_two_suggested_matchings :
    1 - 1 / Real.exp 1 < alpha ∧
    (∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c → ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      ∀ (A I : Type) [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
        (E : Finset (A × I)) (e : I → ℕ) (F blue : Finset (A × Copy e)),
        IsMaxTwoMatching (copyEdges E e) F → IsTSMColoring F blue →
        unifProb (Copy e) (∑ i, e i) (fun ω =>
            c * ((∑ i, e i : ℕ) : ℝ) ≤ (realOPT E (fun t => (ω t).1) : ℝ) ∧
              ((tsmRun blue (F \ blue) ω).card : ℝ) <
                (alpha - ε) * (realOPT E (fun t => (ω t).1) : ℝ))
          ≤ C * Real.exp (-(δ * ((∑ i, e i : ℕ) : ℝ)))) ∧
    (∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      IsMaxTwoMatching (tightE m) (tightFlow m) ∧
        ∀ blue : Finset ((Fin 4 × Fin m) × (Fin 4 × Fin m)),
          IsTSMColoring (tightFlow m) blue → expRatio (tightE m) (tightFlow m) blue ≤ alpha + ε) := by sorry

end FMMM.TSM
