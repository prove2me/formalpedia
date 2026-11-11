-- Prove2me | Theorems.Thm_CosetTreeSVP_SVP_theorem_2_6
-- name    : CosetTreeSVP.SVP.theorem_2_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:34:42.789105+00:00
-- url     : https://prove2.me/theorems/b630cc0e-f27b-401d-ab7d-85fbaa22b151
-- title:
--   Theorem 2.6 — preprocessing n^{−1/3}-BDD: preprocessing in time and space 2^{n/2+o(n)}, constant success probability, advice 2^{o(n)}; deterministic queries in time 2^{o(n)}, polynomial extra space
-- statement:
--   **Theorem 2.6** (time-truncated [ACKS25], via [Hha26]). There are programs $P_{\mathrm{pre}}$, $P_q$ of the randomized rational RAM, a function $g$ with $g(n)/n \to 0$, $K \in \mathbb N$, $c > 0$ and $n_0$ such that for all $n \ge n_0$ and every nonsingular $B \in \mathbb Q^{n\times n}$ of bit length $\ell$:
--
--   - on every coin tape $P_{\mathrm{pre}}$ on $B$ halts within bit time and bit space $2^{n/2+g(n)}(\ell+1)^K$, and its output (the advice) has bit length at most $2^{g(n)}(\ell+1)^K$;
--   - with probability at least $c$ (a measurable event) the advice is successful: for every $n^{-1/3}$-BDD instance $y \in \mathbb Q^n$ of $L(B)$, i.e. $\operatorname{dist}(y, L) < n^{-1/3}\lambda_1(L)$, the run of $P_q$ on the advice and $y$ outputs, on every coin tape, the coefficient vector of the closest lattice vector to $y$, within bit time $2^{g(n)}(\ell+\ell_y+1)^K$ and with at most $(\ell+\ell_y+1)^K$ bits of space beyond the advice.
--
--   The SVP algorithm queries it at the candidate points $\pm dV/\|V\|$.
--
--   Differences from the source:
--   - encoding: 2^{o(n)}, 'constant probability', n large enough for n^{−1/3} < 1/2 → one g with g(n)/n → 0, c > 0, n₀, chosen before n and B; reason: the paper's convention (p. 11): n tends to infinity and every o, O, Ω is uniform over the parameters; the functions and constants are chosen after the fixed t and before n, the basis, d and v
--   - encoding: a randomized classical preprocessing algorithm and a query algorithm, worst-case time and space, 'polynomial factors in the bit length of the inputs' (p. 11) → programs Ppre, Pq of TwMSOCount.Main; bit time and bit space on every coin tape times (ℓ+1)^K (preprocessing) and (ℓ+ℓ_y+1)^K (queries); reason: the paper's cost convention (p. 11)
--   - encoding: 'succeeds with constant probability' → the success event (preprocessing outputs a successful advice) is measurable and has fair-coin probability ≥ c for a constant c > 0; reason: measurability makes the probability well defined; the constant is fixed before n and B
--   - encoding: 'deterministically solved' → on every coin tape the query halts with the correct output within the bounds; reason: a deterministic run is one whose correctness and cost do not depend on the coins
--   - encoding: 'polynomial additional space' → bit space ≤ the advice's stored bits + (ℓ+ℓ_y+1)^K; reason: space beyond storing the advice
--   - encoding: the instance is given by a basis of L and a target y → the query input is the advice followed by y ∈ ℚⁿ; the basis is available to the preprocessing; reason: the advice may carry the basis (it has ℓ ≤ (ℓ+1)^K bits)
-- source:
--   Hhan, Finding a Shortest Vector and More in 2^{n/2+o(n)} Time using q-ary Coset Difference Tree, arXiv:2609.02764 (held version, sha256 687602f4…), p. 12 (PDF 14), Theorem 2.6

import Mathlib
import Definitions.Def_TwMSOCount_Main_Machine
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_SuperlatSVP_SolvesSVPWithin
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Definitions.Def_CosetTreeSVP_SVP_Basics
import Definitions.Def_CosetTreeSVP_SVP_Tree
import Definitions.Def_CosetTreeSVP_SVP_Algo

open MeasureTheory Filter Topology TwMSOCount.Main
open scoped ENNReal

namespace CosetTreeSVP.SVP

theorem theorem_2_6 :
    ∃ (Ppre Pq : Program) (g : ℕ → ℝ) (K : ℕ) (c : ℝ),
      Tendsto (fun n => g n / n) atTop (𝓝 0) ∧ 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ B : Matrix (Fin n) (Fin n) ℚ, B.det ≠ 0 →
        (∀ τ : ℕ → Bool, ∃ s : RunStats,
            runStats Ppre τ (Config.init (SuperlatSVP.encBasis B)) = some s ∧
            (s.time : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2 + g n) *
              ((SuperlatSVP.inputBits B : ℝ) + 1) ^ K ∧
            (s.space : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2 + g n) *
              ((SuperlatSVP.inputBits B : ℝ) + 1) ^ K ∧
            (wordBits s.final.output : ℝ) ≤ (2 : ℝ) ^ g n *
              ((SuperlatSVP.inputBits B : ℝ) + 1) ^ K) ∧
        MeasurableSet (preSuccess Ppre Pq g K B) ∧
        ENNReal.ofReal c ≤ coinTape (preSuccess Ppre Pq g K B) := by sorry

end CosetTreeSVP.SVP
