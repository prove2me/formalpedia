-- Prove2me | Theorems.Thm_FMMM_TSM_tsm_assigned_iff
-- name    : FMMM.TSM.tsm_assigned_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:23:55.389734+00:00
-- url     : https://prove2.me/theorems/281e3479-1ded-417e-b7d3-a4d9402dff06
-- title:
--   §4.2.2, p. 7: when the TSM algorithm assigns an ad
-- statement:
--   Throughout §4.2 until the final proof of Theorem 5 the paper assumes $e_i = 1$ for every impression type: there are $n = |J|$ impression types and $n$ impressions are drawn i.i.d. uniformly from them.
--
--   Let $F$ be a maximum 2-matching of $E$ (the integral max flow of $G_f$) with a TSM colouring, and let $N_j(\omega)$ be the number of arrivals of type $j$ in the arrival sequence $\omega$. Then for every arrival sequence and every ad $a$, the algorithm assigns $a$ if and only if there is a type $j$ such that
--
--   $$\big((a, j) \text{ is blue and } N_j(\omega) \ge 1\big) \quad\text{or}\quad \big((a, j) \text{ is red and } N_j(\omega) \ge 2\big).$$
--
--   This turns the analysis of $\mathrm{ALG}$ into balls-in-bins questions: an ad of $A_B$ is chosen iff its impression is drawn, and an ad of $A_{BR}$ is chosen iff its blue impression is drawn at least once or its red impression at least twice.
--
--   Differences from the source:
--   - generalization: for a ∈ A_B: a is chosen iff its impression is drawn; for a ∈ A_BR: if |D(i_b)| ≥ 1 or |D(i_r)| ≥ 2 then a is chosen → for every ad a: a is assigned iff some blue edge (a, j) has N_j ≥ 1 or some red edge (a, j) has N_j ≥ 2; reason: the same argument for every ad; it specializes to the paper's two statements for A_B and A_BR
--   - encoding: the instance with e_i = 1 for all i (standing assumption of §4.2 until the final proof), draws i.i.d. uniform on I, n = |I| = m → impression types J with n = Fintype.card J and arrivals ω : Fin n → J uniform; reason: the standing assumption of the section, written into the types; same instances
--   - encoding: integral maximum s–t flow of the boosted flow graph G_f (capacities 2, 1, 2) with unit-flow edge set E_f → a maximum 2-matching F of E (IsMaxTwoMatching E F), with E_f = F; reason: integral flows of G_f are exactly the subgraphs of E with all degrees ≤ 2 and the flow value is the number of edges; same objects
--   - encoding: the four colouring rules of §4.2.1 applied to the paths and cycles of E_f → IsTSMColoring F blue: an explicit decomposition of F into vertex-disjoint pieces (whole paths, cycles), each coloured by the rule of its type, with the starting point and orientation of each piece existential; red = F \ blue; reason: the existential orientation is exactly the freedom left by "alternating"; same set of colourings
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.2, p. 7 (unnumbered)

import Mathlib
import Definitions.Def_FMMM_TSM_IsMaxTwoMatching
import Definitions.Def_FMMM_TSM_IsTSMColoring
import Definitions.Def_FMMM_TSM_tsmRun

namespace FMMM.TSM

/-- **When the TSM algorithm assigns an ad.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.2, p. 7 (unnumbered): "Consider some a ∈ A_B with blue edge (a, i). The event that a is
ever chosen is exactly the event that some i′ ∈ D(i) is ever drawn from D, since then we will
choose a (and no other impression will choose a). … Now consider some a ∈ A_BR with blue edge
(a, i_b) and red edge (a, i_r). If |D(i_b)| ≥ 1, or if |D(i_r)| ≥ 2, then a will definitely be
chosen."

Unit instance (`e_i = 1`, `n = |J|` arrivals): for a maximum 2-matching `F` with a TSM colouring,
every arrival sequence `ω` and every ad `a`, `a` is assigned by the run iff for some type `j`,
either `(a, j)` is blue and `j` arrives at least once, or `(a, j)` is red and `j` arrives at least
twice.

**Formalization Note.** The paper states the "if" direction for `A_BR` and the equivalence for
`A_B`; the equivalence is stated here for every ad (the same argument). -/
theorem tsm_assigned_iff {A J : Type} [DecidableEq A] [Fintype J] [DecidableEq J]
    (E F blue : Finset (A × J)) (hF : IsMaxTwoMatching E F) (hc : IsTSMColoring F blue)
    (ω : Fin (Fintype.card J) → J) (a : A) :
    a ∈ tsmRun blue (F \ blue) ω ↔
      ∃ j : J, ((a, j) ∈ blue ∧ 1 ≤ (Finset.univ.filter (fun t => ω t = j)).card) ∨
        ((a, j) ∈ F \ blue ∧ 2 ≤ (Finset.univ.filter (fun t => ω t = j)).card) := by sorry

end FMMM.TSM
