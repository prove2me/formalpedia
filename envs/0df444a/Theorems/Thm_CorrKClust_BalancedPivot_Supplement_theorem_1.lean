-- Prove2me | Theorems.Thm_CorrKClust_BalancedPivot_Supplement_theorem_1
-- name    : CorrKClust.BalancedPivot.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:27:20.663477+00:00
-- url     : https://prove2.me/theorems/9a4dd7a9-8876-4365-8f3d-87cfc37c12a9
-- title:
--   Theorem 1 — uniform polynomial-time approximation conversion
-- statement:
--   Fix $\alpha\ge1$ and any actual polynomial-time $\alpha$-approximation algorithm $A$ for unconstrained correlation clustering. There is a computable family of algorithms giving the stated guarantee at every positive rational accuracy. For every requested real $\varepsilon>0$, a positive rational accuracy $q\le\varepsilon$ selects an algorithm running in polynomial time, uniformly over all $n$ and $1\le k\le n$, whose legal output $f$ satisfies
--   $$\operatorname{Cost}_G(f)\le[1+2\alpha+(1+\alpha)\varepsilon]\operatorname{OPT}_k(G).$$
--   Each fixed accuracy has its own polynomial runtime bound. This is a PTAS-based conversion for variable $k$, without an FPTAS claim. The family is computable jointly in its rational parameter and binary input; the runtime and output certificates refer to actual Turing-machine transducers.
--
--   Differences from the source:
--   - generalization: factor 1+2α+O(ε) → factor 1+2α+(1+α)ε; reason: printed p.16 gives (1+ε)OPT_k+(2+ε)Cost(C), which supplies this explicit coefficient
--   - encoding: polynomial-time algorithms for every fixed accuracy → a computable rational-accuracy family with Cook polynomial-time certificates for every positive rational accuracy; reason: any rational accuracy below a positive requested real accuracy suffices; the exponent may depend on accuracy, while the same program handles all n,k
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Rajmohan Rajaraman, Omer Wasim, Tegan Wilson, STOC 2027 submission #302 (October 2026), Theorem 1, p. 15

import Definitions.Def_CorrKClust_BalancedPivot_Supplement_Offline

set_option autoImplicit false
open Classical
noncomputable section

namespace CorrKClust.BalancedPivot.Supplement

/-- Theorem 1, printed pp.15–16. A single program is uniform in n and variable k.
For each fixed accuracy it has a polynomial bound; no bound polynomial in 1/ε is asserted.
The factor is the proof's penultimate inequality, without an instance-dependent O constant. -/
theorem theorem_1 (α : ℝ) (A : List Bool → List Bool) (hA : CCApprox α A) :
    ∃ scheme : ℚ → List Bool → List Bool, Computable₂ scheme ∧
      ∀ q : ℚ, 0 < q →
        KApprox (1 + 2 * α + (1 + α) * (q : ℝ)) (scheme q) := by sorry

end CorrKClust.BalancedPivot.Supplement
