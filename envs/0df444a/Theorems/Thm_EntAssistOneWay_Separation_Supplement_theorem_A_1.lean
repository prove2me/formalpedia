-- Prove2me | Theorems.Thm_EntAssistOneWay_Separation_Supplement_theorem_A_1
-- name    : EntAssistOneWay.Separation.Supplement.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:52:13.491794+00:00
-- url     : https://prove2.me/theorems/0446e204-e6a2-4c71-bb13-7b81b386f568
-- title:
--   Theorem A.1 — entanglement-assisted SMP protocol for shifted equality
-- statement:
--   There are absolute constants $c_1,c_2,c_3>0$ such that for every finite group $G$ with $|G|\ge2$ and every integer $r\ge1$ the following holds. Let $S=\mathbb F_2^r$; in $\mathrm{ShiftEq}_{G,r}$ Alice holds $g_1,g_2:S\to G$, Bob holds $h:S\to G$ and $s\in S$, and the answer is $1$ iff $g_1(x)g_2(x+s)=h(x)$ for all $x\in S$. There is an entanglement-assisted SMP protocol with $q$ qubits per player and $c_A+c_B$ bits of communication such that
--
--   $$c_A+c_B\le c_1 r,\qquad c_2\,2^r\log_2|G|\le q\le c_3\,2^r\log_2|G|,$$
--
--   which accepts every yes-instance with probability exactly $1$ and every no-instance with probability at most $1/4$. In particular it computes $\mathrm{ShiftEq}_{G,r}$ with worst-case error at most $1/4$, so $C^{\parallel,*}_{1/4}(\mathrm{ShiftEq}_{G,r})=O(r)$.
--
--   Only Alice and Bob share entanglement, and the referee sees only the two messages. The result shows that shifted equality, whose unassisted one-way complexity is large, is easy even in the weaker entangled SMP model.
--
--   **Formalization Note** The paper writes $O(r)$ and $\Theta(2^r\log|G|)$; $c_1,c_2,c_3$ are quantified before $G$ and $r$.
--
--   Differences from the source:
--   - encoding: O(r) bits and an entangled state on Θ(2^r log|G|) qubits per player → ∃ c₁ c₂ c₃ > 0 before G and r with cA + cB ≤ c₁·r and c₂·2^r·log₂|G| ≤ q ≤ c₃·2^r·log₂|G|; reason: absolute constants, uniform in G and r; both sides of Θ are stated
--   - generalization: an entanglement-assisted SMP protocol (the model allows a randomized referee) → EntangledSMPProtocol with a deterministic referee and no shared randomness besides the entangled state; reason: a protocol of this restricted form is a protocol of the source's model, so the Lean statement implies the source's; Appendix A's protocol has this form
--   - encoding: qubit registers → registers Fin (2^q) for each player; reason: q qubits per player; same instances
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 42, Theorem A.1; pp. 43–44, proof

import Definitions.Def_EntAssistOneWay_Separation_Analysis
import Definitions.Def_EntAssistOneWay_Separation_Probability
import Definitions.Def_EntAssistOneWay_Separation_GroupProblems
import Definitions.Def_EntAssistOneWay_Separation_Supplement_EntangledSMP

open scoped BigOperators ComplexOrder
open Classical
open EntAssistOneWay.Separation
set_option autoImplicit false

namespace EntAssistOneWay.Separation.Supplement

noncomputable section

/-- Theorem A.1, p. 42: an entanglement-assisted SMP protocol for shifted equality with
`O(r)` bits, `Θ(2^r log |G|)` qubits per player, perfect completeness and soundness error
at most `1/4`; in particular worst-case error at most `1/4`. -/
theorem theorem_A_1 :
    ∃ c₁ c₂ c₃ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧
      ∀ (G : Type) [Group G] [Fintype G], 2 ≤ Fintype.card G →
      ∀ r : ℕ, 1 ≤ r →
      ∃ (q cA cB : ℕ) (P : EntangledSMPProtocol (ShiftAlice G r) (ShiftBob G r) q cA cB),
        ((cA + cB : ℕ) : ℝ) ≤ c₁ * r ∧
        c₂ * 2 ^ r * log₂ (Fintype.card G) ≤ q ∧
        (q : ℝ) ≤ c₃ * 2 ^ r * log₂ (Fintype.card G) ∧
        (∀ a b, shiftEq r a b = true → entangledSMPAccept P a b = 1) ∧
        (∀ a b, shiftEq r a b = false → entangledSMPAccept P a b ≤ 1 / 4) ∧
        ComputesWithError (shiftEq r) (entangledSMPAccept P) (1 / 4) := by sorry

end

end EntAssistOneWay.Separation.Supplement
