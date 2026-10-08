-- Prove2me | Theorems.Thm_CongestionPoA_AsymMax_theorem6_lower
-- name    : CongestionPoA.AsymMax.theorem6_lower
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T17:33:03.907765+00:00
-- url     : https://prove2.me/theorems/e263155b-544c-40bc-80f6-ae9d6558bb8a
-- title:
--   Theorem 6 — square-root lower-bound instances
-- statement:
--   For every integer $k\ge2$, set $N=k(k-1)+1$. There is a finite congestion game with $N$ players and $kN$ facilities, all with identity latency $f_e(n)=n$, with a pure Nash profile $A$ and an optimal profile $P$ such that
--
--   $$\operatorname{MAX}(A)=k^2,\qquad \operatorname{MAX}(P)=k.$$
--
--   Every feasible profile $Q$ satisfies $\operatorname{MAX}(Q)\ge k$, so $P$ is optimal. Thus the price of anarchy is at least $k$, and $k\ge\sqrt N$. These positive exact costs prevent a zero-latency witness from making the ratio claim empty.
--
--   **Formalization Note** The paper prints the alternative strategy index as $\lceil(i-1)/k\rceil$; its Nash assertion and Figure 2 require $\lceil(i-1)/(k-1)\rceil$. The theorem captures the finite congestion-game instance; it does not encode the separate network realization.
-- source:
--   Christodoulou and Koutsoupias, The Price of Anarchy of Finite Congestion Games, STOC 2005, DOI 10.1145/1060590.1060600, PDF pp. 4–5, Theorem 6 and proof; Figure 2

import Definitions.Def_CongestionPoA_AsymMax_Model

set_option autoImplicit false

namespace CongestionPoA.AsymMax

/-- Christodoulou and Koutsoupias, STOC 2005, Theorem 6 and proof, PDF pp. 4–5.
Formalization Note: with `N = k(k−1)+1`, the facility type has exactly `kN` elements.
The identity latency, exact costs `k²` and `k`, and optimality of `P` rule out
a zero-cost or nonoptimal comparison witness.
The paper prints the alternative facility index as `⌈(i−1)/k⌉`; its Figure 2 and
the Nash claim require `⌈(i−1)/(k−1)⌉`. This statement formalizes the corrected
finite congestion-game construction; its network realization is not encoded here. -/
theorem theorem6_lower (k : ℕ) (hk : 2 ≤ k) :
    let N := k * (k - 1) + 1
    letI : Nonempty (Fin N) := ⟨⟨0, Nat.succ_pos _⟩⟩
    ∃ (G : CongestionGame (Fin N) (Fin (k * N)))
      (A P : Fin N → Finset (Fin (k * N))),
      IsLinear G ∧
      (∀ e n, G.latency e n = (n : ℝ)) ∧
      IsPureNash G A ∧ IsProfile G P ∧
      maxCost G A = (k : ℝ) ^ 2 ∧ maxCost G P = (k : ℝ) ∧
      (∀ Q, IsProfile G Q → (k : ℝ) ≤ maxCost G Q) := by sorry

end CongestionPoA.AsymMax
