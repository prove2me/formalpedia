-- Prove2me | Theorems.Thm_DworczakDACC_claim_5
-- name    : DworczakDACC.claim_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:57:13.97617+00:00
-- url     : https://prove2.me/theorems/b777fdc9-e4f5-4479-91d0-da726262bf1a
-- title:
--   Claim 5 — after $k^\star$, $d^k$ strictly decreases or $|X^k|$ strictly grows (corrected: stack exit when no acceptable partner remains)
-- statement:
--   Let $\Phi$ name every agent infinitely often and fix any order of blocks (a)/(b). Let $k^\star$ be a round such that the applicant sets at the end of every round $k\ge k^\star$ equal those at the end of round $k^\star$ (the sets $A^k_i$ never shrink, so such a round exists). Write $d^k=d(\mathcal B^k,\mu^k)$ and $d^k_i=d_i(\mathcal B^k,\mu^k)$. Then for every round $k>k^\star$, unless $d^{k-1}_{\Phi(k)}=0$,
--
--   $$d^k<d^{k-1}\qquad\text{or}\qquad |X^{k-1}|<|X^k| .$$
--
--   Here $X^k$ is the set of man–woman pairs that never interact after round $k$. The claim is the inductive step of Lemma 1: a non-deceptive divorce after $k^\star$ puts a pair in $X^k$ for good, and otherwise the distance to stability strictly falls.
--
--   Differences from the source:
--   - correction: Algorithm 1, step 4(b)iii (p. 8): remove i from CC if µ(i) ≠ ∅ or Bᵢ = ∅ → remove i from CC if µ(i) ≠ ∅ or argmax{Bᵢ ∪ {∅}; ≻ⁱ} = ∅ (no acceptable partner left in Bᵢ); reason: budgets start full and unacceptable partners never leave them, so a compensated agent with no acceptable partner left applies to ∅ forever under the printed test; in the market m1: w2; m2: w2 ≻ w1; m3: w3 ≻ w1; w1: m2 ≻ m3 ≻ m1; w2: m3 ≻ m1 ≻ m2; w3: nobody, with Φ = m2, w1, m1, w1, (m1, m2, m3, w1, w2, w3) repeated, m3 is stuck on CC from round 6 on and DACC never stops; the corrected test is the paper's own footnote 7 convention and coincides with the printed one when every partner is acceptable; the claim concerns rounds, whose end is undefined when the printed rule leaves an agent stuck on CC
--   - encoding: d^{k−1}_{Φ(k)} with rounds k = 1, 2, … and Φ indexed from 1 → agentPotential (roundState (k − 1)) (Φ (k − 1)) with Φ indexed from 0; reason: round k of the paper is the application of Φ (k − 1); same instances
--   - encoding: (B^k, µ^k, A^k) at the end of round k; X^k → roundState k (the state at the first time after k order-proposals with an empty stack, or the stopped state); neverAfter k, a Finset (D × H); reason: the stack is empty exactly between rounds; a man–woman pair is an element of D × H
--   - reading: "i and j interact" (not defined; used in the proofs of Claim 1 and Claim 5) → Interacts: one applies to the other (an actual application) or they are divorced, at that time step; reason: the proofs name exactly these events ("applied to j and was rejected", "were matched and j divorced i", "l can never apply to l′"); a divorce must count, otherwise the pair divorced in round k would already lie in X^{k−1}
--   - generalization: the round k⋆ after which all A^k_i are constant → any kstar with that property; reason: the paper's k⋆ has the property, so the statement specializes to it
--   - generalization: items (a) and (b) of "i applies" executed in some order (footnote a, p. 8: "in any order, even random") → the order is a parameter ord : ℕ → Bool (one choice per time step), universally quantified; reason: every resolution of footnote a, including a random one along each sample path, is some ord
-- source:
--   Dworczak, Deferred Acceptance with Compensation Chains (working paper, Nov 9, 2017), Appendix A, Claim 5, p. 23

import Mathlib
import Definitions.Def_RuralHospitals_Market
import Definitions.Def_DworczakDACC_IsAdmissible
import Definitions.Def_DworczakDACC_agentPotential
import Definitions.Def_DworczakDACC_potential
import Definitions.Def_DworczakDACC_roundState
import Definitions.Def_DworczakDACC_neverAfter

namespace DworczakDACC

open RuralHospitals

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq D] [DecidableEq H]

/-- **Claim 5: after the applicant sets settle, in every round either `d` strictly decreases or
`|Xᵏ|` strictly grows, unless the round's proposer is already satisfied.**
Dworczak, *Deferred Acceptance with Compensation Chains* (working paper, Nov 9, 2017), Appendix A,
Claim 5, p. 23: "For every k > k⋆, unless d^{k−1}_{Φ(k)} = 0, either d^k decreases strictly or
|X^k| grows strictly." Context, p. 23: "the sets A^k_i never shrink. Thus, for a fixed Φ, there
exists a round k⋆ such that all A^k_i are constant after k⋆."

Let `Φ` name every agent infinitely often, `ord` be any (a)/(b) order, and `k⋆` be a round such
that the applicant sets `Aᵏᵢ` at the end of every round `k ≥ k⋆` equal those at the end of round
`k⋆`. Then for every round `k > k⋆` such that the proposer of round `k` has
`d^{k−1}_{Φ(k)} ≠ 0`:
`d(Bᵏ, µᵏ) < d(Bᵏ⁻¹, µᵏ⁻¹)` or `|Xᵏ⁻¹| < |Xᵏ|`.

**Formalization Note.** Round `k` (paper, `k ≥ 1`) is the application of `Φ (k - 1)` (0-based
`Φ`), so the paper's `d^{k−1}_{Φ(k)}` is `agentPotential Mk (roundState … (k - 1)) (Φ (k - 1))`.
End-of-round states are `roundState` (the state when the stack has emptied after the round's
order-proposal), and `Xᵏ` is `neverAfter … k`. The claim is stated for every `k⋆` with the
constancy property, which includes the paper's `k⋆`. The run uses the corrected stack exit. -/
theorem claim_5 (Mk : Market D H) (Φ : ℕ → D ⊕ H) (hΦ : IsAdmissible Φ) (ord : ℕ → Bool)
    (kstar : ℕ)
    (hstar : ∀ k, kstar ≤ k →
      (roundState Mk Φ ord k).appM = (roundState Mk Φ ord kstar).appM ∧
        (roundState Mk Φ ord k).appW = (roundState Mk Φ ord kstar).appW)
    (k : ℕ) (hk : kstar < k)
    (hd : agentPotential Mk (roundState Mk Φ ord (k - 1)) (Φ (k - 1)) ≠ 0) :
    potential Mk (roundState Mk Φ ord k) < potential Mk (roundState Mk Φ ord (k - 1)) ∨
      (neverAfter Mk Φ ord (k - 1)).card < (neverAfter Mk Φ ord k).card := by sorry

end DworczakDACC
