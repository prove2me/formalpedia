-- Prove2me | Theorems.Thm_CFLOutliers_appendixB_approximation
-- name    : CFLOutliers.appendixB_approximation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:41:52.894465+00:00
-- url     : https://prove2.me/theorems/5293067c-0fd6-4e3f-9c4b-77364f923ace
-- title:
--   Appendix B — the complete quota algorithm returns a feasible $(60/11+\varepsilon)$-approximate solution
-- statement:
--   Let the instance satisfy the standing assumptions and have a capacity-feasible solution serving at least $q$ clients, and let $0<\varepsilon\le 1$. Then
--
--   1. the complete quota algorithm of Appendix B has an output;
--   2. every output $S$ is capacity-feasible, serves at least $q$ clients, and satisfies
--   $$c(S)\le\Bigl(\frac{60}{11}+\varepsilon\Bigr)\mathrm{OPT}.$$
--
--   This is the approximation half of Theorem 1.1: it combines Theorem 2.1, Lemma 2.2, the warm-start relation, the bound (7), the scale choice (20) and the opening-cost restoration of §2.2.
--
--   Differences from the source:
--   - generalization: a finite metric space with distances c → a pseudometric on the index set F ⊔ C (distinct points may be at distance 0); reason: it covers every metric instance, including a facility co-located with a client; no step of the paper uses positivity of distances
--   - generalization: the algorithm's run, merging S_{k−1} and S_k "using Lemma 2.2" → every execution of the procedure: every run of Local and every merged solution meeting Lemma 2.2's bound (3); reason: the procedure leaves the optimal assignments, the improving changes and the merge open; the construction of Appendix A meets (3), so the paper's algorithm is one execution
--   - generalization: rational input data → real opening costs and distances; reason: the guarantee is about costs only; rational instances are a special case
--   - encoding: "discard facilities costing more than M" → the modified instance has only the retained facilities, renumbered by a fixed bijection; reason: Lean convention; the same instance up to renaming
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), Appendix B, "Approximation guarantee", p.14; §2.2 "Absorbing the opening charge", p.6

import Mathlib
import Definitions.Def_CFLOutliers_QuotaOut

namespace CFLOutliers

/-- **Approximation guarantee of the complete quota algorithm** (Dabas, arXiv:2611.04094,
Appendix B, "Approximation guarantee", p.14, with §2.2 "Absorbing the opening charge", p.6).
For an instance satisfying the standing assumptions that has a feasible solution and every real
`0 < ε ≤ 1`:
1. the procedure of Appendix B has an output;
2. every output is capacity-feasible, serves at least `q` clients and costs at most
   `(60/11 + ε) OPT`.

**Formalization Note.** `QuotaOut I ε` admits every execution of the procedure (every run of
`Local`, every merged solution meeting Lemma 2.2's bound); the statement holds for all of them. -/
theorem appendixB_approximation (I : Inst) (hI : I.Std) (hF : I.Feasible) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (∃ S, QuotaOut I ε S) ∧
    ∀ S, QuotaOut I ε S →
      S.CapFeasible ∧ I.q ≤ (served S).card ∧ cost S ≤ (60 / 11 + ε) * OPT I := by sorry

end CFLOutliers
