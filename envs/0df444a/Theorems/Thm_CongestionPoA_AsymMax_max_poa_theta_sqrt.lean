-- Prove2me | Theorems.Thm_CongestionPoA_AsymMax_max_poa_theta_sqrt
-- name    : CongestionPoA.AsymMax.max_poa_theta_sqrt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:47:49.744147+00:00
-- url     : https://prove2.me/theorems/18523094-a097-4730-9cfd-d2b419096a51
-- title:
--   Theorems 5–6 — maximum-cost price of anarchy grows as sqrt N
-- statement:
--   The pure maximum-cost price of anarchy in finite linear congestion games has square-root order in the number of players. The upper statement holds for every $N\ge1$, every pure Nash profile $A$, and every feasible profile $P$:
--
--   $$\operatorname{MAX}(A)\le\left(1+\sqrt{\frac{5N}{2}}\right)\operatorname{MAX}(P).$$
--
--   For every integer $k\ge2$, there is an identity-latency game with $N=k(k-1)+1$ players and $kN$ facilities, a pure Nash profile $A$, and an optimal profile $P$ with
--
--   $$\operatorname{MAX}(A)=k^2,\qquad\operatorname{MAX}(P)=k.$$
--
--   Every feasible profile $Q$ in each lower instance has $\operatorname{MAX}(Q)\ge k$. The upper inequality bounds the ratio against an optimal profile; the lower instances attain ratio $k\ge\sqrt N$.
--
--   **Formalization Note** Linear means affine with nonnegative coefficients. The lower construction uses the corrected strategy index described under Theorem 6; the network realization is outside this statement.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF pp. 4–5, Theorems 5 and 6

import Mathlib
import Definitions.Def_CongestionPoA_AsymMax_Model

set_option autoImplicit false

namespace CongestionPoA.AsymMax

/-- Christodoulou and Koutsoupias, STOC 2005, Theorems 5 and 6,
PDF pp. 4–5. The pure maximum-cost price of anarchy has order `√N`.
Formalization Note: the first clause is the proof's explicit upper bound for
every feasible comparison profile. The second fixes `N = k(k−1)+1` and
`kN` facilities with identity latencies, exact positive costs `k²`, `k`, and
optimality of the comparison profile.
It records the corrected denominator `k−1` implicit in Figure 2; the
paper's printed `k` makes the proposed profile fail to be Nash. The
network realization mentioned in Theorem 6 is not encoded. -/
theorem max_poa_theta_sqrt :
    (∀ (N : ℕ) (hN : 1 ≤ N),
      letI : Nonempty (Fin N) := ⟨⟨0, Nat.zero_lt_of_lt hN⟩⟩
      ∀ (E : Type) [Fintype E] [DecidableEq E]
        (G : CongestionGame (Fin N) E) (A P : Fin N → Finset E),
        IsLinear G → IsPureNash G A → IsProfile G P →
          maxCost G A ≤ (1 + Real.sqrt ((5 / 2 : ℝ) * N)) * maxCost G P) ∧
    (∀ (k : ℕ) (_hk : 2 ≤ k),
      let N := k * (k - 1) + 1
      letI : Nonempty (Fin N) := ⟨⟨0, Nat.succ_pos _⟩⟩
      ∃ (G : CongestionGame (Fin N) (Fin (k * N)))
        (A P : Fin N → Finset (Fin (k * N))),
        IsLinear G ∧
        (∀ e n, G.latency e n = (n : ℝ)) ∧
        IsPureNash G A ∧ IsProfile G P ∧
        maxCost G A = (k : ℝ) ^ 2 ∧ maxCost G P = (k : ℝ) ∧
        (∀ Q, IsProfile G Q → (k : ℝ) ≤ maxCost G Q)) := by sorry

end CongestionPoA.AsymMax
