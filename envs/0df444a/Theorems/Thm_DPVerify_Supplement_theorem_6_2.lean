-- Prove2me | Theorems.Thm_DPVerify_Supplement_theorem_6_2
-- name    : DPVerify.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:58:26.37402+00:00
-- url     : https://prove2.me/theorems/0afe1944-5e7e-4a9a-ad09-30d08ba47ebd
-- title:
--   Theorem 6.2 — an AM tester correct with probability $5/6$ becomes an $\varepsilon$-DP AM tester correct with probability $2/3$ on $\lceil6/\varepsilon\rceil s$ samples
-- statement:
--   Let $T$ be a public-coin (AM) distribution tester with any number of rounds, sample complexity $s$ and communication complexity $c$, on a measurable space $\mathcal X$, and let $\mathrm{Yes}$, $\mathrm{No}$ be sets of distributions on $\mathcal X$. Suppose $T$ tests $\mathrm{Yes}$ against $\mathrm{No}$ with probability $5/6$:
--
--   1. for every $D\in\mathrm{Yes}$ some adaptive (honest) prover strategy makes the verifier accept with probability at least $5/6$;
--   2. for every $D\in\mathrm{No}$ every adaptive prover strategy makes the verifier accept with probability at most $1/6$.
--
--   Then for every $\varepsilon>0$ there is an AM tester $T'$ with sample complexity exactly $\lceil 6/\varepsilon\rceil\cdot s$ and communication complexity exactly $c$ that is $\varepsilon$-differentially private (over its whole transcript, against every prover strategy) and tests $\mathrm{Yes}$ against $\mathrm{No}$ with probability $2/3$:
--   $$D\in\mathrm{Yes}\Rightarrow\exists\text{ adaptive }g:\ \Pr[T'\text{ accepts}]\ge\tfrac23,\qquad D\in\mathrm{No}\Rightarrow\forall\text{ adaptive }g:\ \Pr[T'\text{ accepts}]\le\tfrac13 .$$
--
--   This extends the generic private-tester reduction of [ADR18, ADR17] from testers to public-coin interactive proofs: privacy costs a factor $\lceil 6/\varepsilon\rceil$ in samples and nothing in communication.
--
--   **Formalization Note** The tester model is `DPVerify.Supplement.MultiAMProtocol`; deterministic strategies suffice on both sides since randomized provers are mixtures. "$\xi$-approximately satisfies $\mathcal P$" enters only through the sets $\mathrm{Yes}$ and $\mathrm{No}$.
--
--   Differences from the source:
--   - generalization: "test whether $D$ $\xi$-approximately satisfies $\mathcal P$ with probability $q$" (the paper does not say whether the yes-instances are $\mathcal P$ or its $\xi$-neighbourhood, §2 and Lemma 6.1) → completeness and soundness at level $q$ for arbitrary sets $\mathrm{Yes}$, $\mathrm{No}$ of distributions; reason: the proof transfers correctness distribution by distribution, and every reading of the property is an instance.
--   - generalization: $\varepsilon$-DP against "any adversary" → against every deterministic prover strategy, adaptive or not; reason: a stronger privacy conclusion; adaptive strategies are among them.
--   - encoding: AM tester, its communication and adjacency → `MultiAMProtocol` (uniform public bits per round, finite reply sets, private coins of the decision folded into an acceptance probability), communication $\sum_i n_i+\sum_i\lceil\log_2|B_i|\rceil$, substitution neighbours of fixed-size samples; reason: §2's AM model and the paper's adjacency for fixed-size samples (§6, p.33: "neighboring datasets which differ on the $i$th coordinate").
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Theorem 6.2, p.32 (PDF p.35); proof pp.32–33 (PDF pp.35–36)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_DPVerify_Supplement_MultiAMProtocol

set_option autoImplicit false

open MeasureTheory

namespace DPVerify.Supplement

/-- Theorem 6.2 (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution
Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), p.32 = PDF p.35,
proof pp.32–33): an AM distribution tester `T` with sample complexity `s` and communication
complexity `c` that is correct with probability `5/6` yields, for every `ε > 0`, an `ε`-DP AM
tester `T′` with sample complexity `⌈6/ε⌉ · s` and communication complexity `c` that is correct
with probability `2/3`.

**Formalization Note**
* "`T` can test whether `D` ξ-approximately satisfies `P` with probability `q`" is read as
  completeness and soundness at level `q` for arbitrary sets `Yes`, `No` of distributions: on
  `D ∈ Yes` some adaptive (honest) prover strategy is accepted with probability `≥ q`; on
  `D ∈ No` every adaptive prover strategy is accepted with probability `≤ 1 − q`. `Yes`, `No`
  specialize to `P` (or its ξ-neighbourhood) and the distributions ξ-far from `P`.
* `T` has any number of rounds (`MultiAMProtocol`); deterministic strategies suffice on both
  sides (randomized provers are mixtures).
* The sample size of `T′` is exactly `⌈6/ε⌉₊ * s`, its communication is equal to `T.comm`, and
  it is `(ε, 0)`-DP over its whole transcript (coins, replies, decision bit) against every prover
  strategy. -/
theorem theorem_6_2 {X : Type} [MeasurableSpace X] {s : ℕ} (T : MultiAMProtocol X s)
    (Yes No : Set (ProbabilityMeasure X))
    (hcompl : ∀ D ∈ Yes, ∃ g, T.IsAdaptive g ∧ (5 / 6 : ℝ) ≤ T.accept g D)
    (hsound : ∀ D ∈ No, ∀ g, T.IsAdaptive g → T.accept g D ≤ 1 / 6)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T' : MultiAMProtocol X (⌈6 / ε⌉₊ * s),
      T'.comm = T.comm ∧ T'.IsDP ε 0 ∧
      (∀ D ∈ Yes, ∃ g, T'.IsAdaptive g ∧ (2 / 3 : ℝ) ≤ T'.accept g D) ∧
      (∀ D ∈ No, ∀ g, T'.IsAdaptive g → T'.accept g D ≤ 1 / 3) := by sorry

end DPVerify.Supplement
