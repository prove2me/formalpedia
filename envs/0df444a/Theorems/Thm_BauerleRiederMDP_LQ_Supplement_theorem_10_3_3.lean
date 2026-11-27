-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_10_3_3
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_10_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:08:24.07314+00:00
-- url     : https://prove2.me/theorems/4aef0b20-ffc5-5dd7-a708-16678c7bbcac
-- title:
--   Theorem 10.3.3 — secretary problem: reject the first k*, then take the first record; success probability (k*/N) h(k*)
-- statement:
--   The optimal stopping time for the secretary problem is as follows: make interviews with the first $k^*$ candidates and reject them all ($k^*$ given by (10.5)); afterwards take the first candidate who is better than her predecessors. The probability for choosing the best candidate is then $(k^*/N) h(k^*)$.
--
--   **Formalization Note.** $N > 2$, the case in which (10.5) defines $k^*$ (p.322). The candidates arrive in uniformly random order; optimality is among all stopping rules based on relative ranks (`IsRelRankStoppingTime`), and the threshold rule is itself one. The probability is `secretarySuccessProb`, the uniform-permutation probability that the accepted candidate is the best; it is not defined through the recursion of p.321.
--
--   Differences from the source:
--   - encoding: stopping times of the record chain (X_n), sup_{τ≤N−1} ℙ(Z_{X_τ} = N) → stopping rules on the candidates based on relative ranks, uniform permutation; reason: a stopping time of the record chain is a stopping rule and only stopping at a record succeeds; same optimal value
--   - encoding: N ∈ ℕ → N > 2; reason: (10.5) defines k* for N > 2
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 10.3.3, p.323 (PDF 331)

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_secretaryH
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_secretaryKstar
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_IsRelRankStoppingTime
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_secretarySuccessProb
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_secretaryRule

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 10.3.3 (secretary problem)** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), Theorem 10.3.3, p.323, PDF 331, problem of §10.3.3, pp.319–322,
PDF 327–330). The optimal stopping time for the secretary problem is as follows: make interviews
with the first `k*` candidates and reject them all (`k*` given by (10.5)); afterwards take the first
candidate who is better than her predecessors. The probability for choosing the best candidate is
then `(k*/N) h(k*)`.

**Formalization Note.** `N > 2`, the case in which (10.5) defines `k*` (p.322). The candidates
arrive in uniformly random order; optimality is among all stopping rules based on relative ranks
(`IsRelRankStoppingTime`), and the threshold rule is itself one. The probability is
`secretarySuccessProb`, the uniform-permutation probability that the accepted candidate is the best;
it is not defined through the recursion of p.321. -/
theorem theorem_10_3_3 (N : ℕ) (hN : 2 < N) :
    IsRelRankStoppingTime N (secretaryRule N (secretaryKstar N) (by omega)) ∧
    (∀ τ : Equiv.Perm (Fin N) → Fin N, IsRelRankStoppingTime N τ →
      secretarySuccessProb N τ ≤
        secretarySuccessProb N (secretaryRule N (secretaryKstar N) (by omega))) ∧
    secretarySuccessProb N (secretaryRule N (secretaryKstar N) (by omega)) =
      (secretaryKstar N : ℝ) / N * secretaryH N (secretaryKstar N) := by sorry

end BauerleRiederMDP.LQ.Supplement
