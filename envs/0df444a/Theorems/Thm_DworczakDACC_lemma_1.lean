-- Prove2me | Theorems.Thm_DworczakDACC_lemma_1
-- name    : DworczakDACC.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:57:00.657199+00:00
-- url     : https://prove2.me/theorems/c1a2542d-529d-4e11-b255-e3df546829e8
-- title:
--   Lemma 1 — $d$ strictly decreases along a subsequence of rounds (corrected: stack exit when no acceptable partner remains)
-- statement:
--   Let $\Phi$ name every agent infinitely often and fix any order of blocks (a)/(b). There is a strictly increasing sequence of positive integers $(a_n)_{n\in\mathbb N}$ such that, for every $n$ for which DACC($\Phi$) has not stopped by the end of round $a_n$,
--
--   $$d\bigl(\mathcal B^{a_{n+1}},\mu^{a_{n+1}}\bigr)<d\bigl(\mathcal B^{a_n},\mu^{a_n}\bigr).$$
--
--   Since $d$ takes values in $\mathbb N$, this forces the algorithm to stop (Claim 3).
--
--   Differences from the source:
--   - correction: Algorithm 1, step 4(b)iii (p. 8): remove i from CC if µ(i) ≠ ∅ or Bᵢ = ∅ → remove i from CC if µ(i) ≠ ∅ or argmax{Bᵢ ∪ {∅}; ≻ⁱ} = ∅ (no acceptable partner left in Bᵢ); reason: budgets start full and unacceptable partners never leave them, so a compensated agent with no acceptable partner left applies to ∅ forever under the printed test; in the market m1: w2; m2: w2 ≻ w1; m3: w3 ≻ w1; w1: m2 ≻ m3 ≻ m1; w2: m3 ≻ m1 ≻ m2; w3: nobody, with Φ = m2, w1, m1, w1, (m1, m2, m3, w1, w2, w3) repeated, m3 is stuck on CC from round 6 on and DACC never stops; the corrected test is the paper's own footnote 7 convention and coincides with the printed one when every partner is acceptable; the lemma concerns rounds, whose end is undefined when the printed rule leaves an agent stuck on CC
--   - encoding: (a_k)_{k∈ℕ}, with d decreasing along (B^{a_k}, µ^{a_k})_{k=1,2,...} → a : ℕ → ℕ indexed from 0, with the decrease from a 0 on; reason: 0-based indexing of the same sequence
--   - encoding: (B^k, µ^k) and d → roundState k and potential; reason: the end-of-round states and (3.2); same instances
--   - generalization: items (a) and (b) of "i applies" executed in some order (footnote a, p. 8: "in any order, even random") → the order is a parameter ord : ℕ → Bool (one choice per time step), universally quantified; reason: every resolution of footnote a, including a random one along each sample path, is some ord
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), Lemma 1, p. 10 (proof in Appendix A, pp. 23–24)

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Definitions.Def_DworczakDACC_IsAdmissible
import Definitions.Def_DworczakDACC_Stopped
import Definitions.Def_DworczakDACC_potential
import Definitions.Def_DworczakDACC_roundState

namespace DworczakDACC

open RuralHospitals

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq D] [DecidableEq H]

/-- **Lemma 1: the distance to stability strictly decreases along a subsequence of rounds.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017), Lemma 1,
p. 10: "Fixing Φ, there exists a strictly increasing sequence of positive integers (a_k)_{k∈ℕ}
such that d is strictly decreasing along the sequence (B^{a_k}, µ^{a_k})_{k=1,2,...}, for all k
such that DACC(Φ) hasn't yet stopped in round a_k."

For every `Φ` naming every agent infinitely often and every (a)/(b) order `ord` there is a strictly
increasing sequence `a : ℕ → ℕ` of positive integers such that, for every `n`, if the run has not
stopped by the end of round `a n`, then `d(B^{a (n+1)}, µ^{a (n+1)}) < d(B^{a n}, µ^{a n})`.

**Formalization Note.** `(Bᵏ, µᵏ)` is `roundState … k` and `d` is `potential`. "Hasn't yet
stopped in round a_k" is `¬ Stopped (roundState … (a n))`. The sequence is indexed from `0`
and the decrease is required from `a 0` on (the paper's construction starts at `a₀ = k̄`, and its
decrease holds from `a₀` on as well). The run uses the corrected stack exit. -/
theorem lemma_1 (Mk : Market D H) (Φ : ℕ → D ⊕ H) (hΦ : IsAdmissible Φ) (ord : ℕ → Bool) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ n, 0 < a n) ∧
      ∀ n, ¬ Stopped Mk (roundState Mk Φ ord (a n)) →
        potential Mk (roundState Mk Φ ord (a (n + 1))) <
          potential Mk (roundState Mk Φ ord (a n)) := by sorry

end DworczakDACC
