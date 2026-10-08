-- Prove2me | Theorems.Thm_CongestionPoA_AsymMax_theorem5
-- name    : CongestionPoA.AsymMax.theorem5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:33:02.255139+00:00
-- url     : https://prove2.me/theorems/8d865528-4327-43c1-92f9-4efc75684c64
-- title:
--   Theorem 5 — maximum-cost upper bound
-- statement:
--   For every number $N\ge1$ of players, every finite congestion game with nonnegative affine latencies, every pure Nash profile $A$, and every feasible comparison profile $P$,
--
--   $$\operatorname{MAX}(A)\le\left(1+\sqrt{\frac{5N}{2}}\right)\operatorname{MAX}(P).$$
--
--   This is the explicit upper bound proved for the paper's $O(\sqrt N)$ claim. Taking $P$ to minimize maximum cost bounds the pure price of anarchy.
--
--   **Formalization Note** Players are `Fin N`; nonemptiness is required for `MAX`. The proof works for arbitrary feasible $P$, not just an optimum.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF p. 4, Theorem 5 and proof

import Definitions.Def_CongestionPoA_AsymMax_Model

set_option autoImplicit false

namespace CongestionPoA.AsymMax

/-- Christodoulou and Koutsoupias, STOC 2005, Theorem 5 and proof, PDF p. 4.
Formalization Note: `Fin N` has at least one player; the bound is the explicit coefficient
in the proof. It holds for affine nonnegative latencies and every feasible comparison
profile. Pure Nash uses costs, corresponding to negative payoffs in `AGT.IsPureNash`. -/
theorem theorem5 (N : ℕ) (hN : 1 ≤ N) :
    letI : Nonempty (Fin N) := ⟨⟨0, Nat.zero_lt_of_lt hN⟩⟩
    ∀ (E : Type) [Fintype E] [DecidableEq E]
      (G : CongestionGame (Fin N) E) (A P : Fin N → Finset E),
      IsLinear G → IsPureNash G A → IsProfile G P →
        maxCost G A ≤ (1 + Real.sqrt ((5 / 2 : ℝ) * N)) * maxCost G P := by sorry

end CongestionPoA.AsymMax
