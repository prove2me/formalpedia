-- Prove2me | Theorems.Thm_AlgCoverage_OddOrder_sec_9_1_lower
-- name    : AlgCoverage.OddOrder.sec_9_1_lower
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T04:46:30.685491+00:00
-- url     : https://prove2.me/theorems/5006414d-2576-40bf-ab17-7a4cbfb1e20d
-- title:
--   §9.1, lower side — at $k_0$ the hole count has $\mathbb EH=(1+o(1))(N-1)e^{-\lambda_0}$, diverging mean, $\mathrm{Var}(H)/(\mathbb EH)^2=o(1)$, so $H>0$ w.h.p.
-- statement:
--   Let $H$ be the number of missed nonidentity elements after $k_0$ iid uniform inputs in a finite group of odd order $N$. Uniformly over odd-order groups as $N\to\infty$:
--   $$\mathbb EH=(1+o(1))(N-1)e^{-\lambda_0},\qquad \mathbb E[H(H-1)]=(1+o(1))(N-1)(N-2)e^{-2\lambda_0},$$
--   the mean diverges, $\mathrm{Var}(H)/(\mathbb EH)^2=o(1)$, and $H>0$ with high probability. Formally: for every $\varepsilon>0$ and every $C$ there is $N_0$ such that for every odd-order $G$ with $N\ge N_0$ both relative errors are at most $\varepsilon$, $\mathbb EH\ge C$, $(\mathbb EH^2-(\mathbb EH)^2)/(\mathbb EH)^2\le\varepsilon$ and $\Pr(H>0)\ge1-\varepsilon$.
--
--   This is the second-moment step that turns the seed estimate (3.3) into non-coverage at $k_0$.
--
--   Differences from the source:
--   - encoding: every finite group G of odd order → G : Type with [Group G] [Fintype G] and Odd (Fintype.card G); reason: every finite group is isomorphic to one in Type (universe 0), and every quantity in the statement is invariant under isomorphism
--   - encoding: uniformly in odd-order groups, (1 + o(1)) / → 0 / 'eventually' with one error function of N → ∀ ε > 0, ∃ N₀, ∀ G of odd order with |G| ≥ N₀ (and all admissible data); reason: a bound by one function of N tending to zero, independent of the group and data, is exactly this ε–N₀ statement
--   - encoding: probabilities and expectations over iid uniform inputs X ∈ G^k → counting ratios probIid / expIid (sums over G^k divided by N^k); reason: the iid law is uniform on the finite set G^k; same numbers
--   - encoding: sample length k₀ = ⌊c_N − 80⌋ → Int.toNat (k0 N), with λ₀ = (2^{k₀} − 1)/N computed with the integer power; reason: k₀ ≥ 1 for all large N, where the two agree; only eventual (N ≥ N₀) statements use the length
--   - encoding: 'the mean diverges' and 'H > 0 with high probability' → ∀ C, eventually E H ≥ C; and Pr(H > 0) ≥ 1 − ε eventually; reason: definitions of divergence and of 'with high probability', uniformly in G
-- source:
--   Lin, Sharp Second-Order Thresholds for Random Algebraic Coverage, STOC 2027 submission (manuscript sha256 9db96430…), p. 27 (PDF 28), §9.1

import Mathlib
import Definitions.Def_AlgCoverage_OddOrder_Coverage

namespace AlgCoverage.OddOrder

/-- §9.1, lower side (second moment at `k₀`), Lin, printed p. 27 / PDF 28. Let `H` be the number of
missed nonidentity elements after `k₀` iid inputs. Uniformly over odd-order groups as `N → ∞`:
`E H = (1 + o(1))(N − 1)e^{−λ₀}`, `E[H(H − 1)] = (1 + o(1))(N − 1)(N − 2)e^{−2λ₀}`, the mean diverges,
`Var(H)/(E H)² = o(1)`, and `H > 0` with high probability. -/
theorem sec_9_1_lower :
    ∀ ε : ℝ, 0 < ε → ∀ C : ℝ, ∃ N₀ : ℕ, ∀ (G : Type) [Group G] [Fintype G],
      Odd (Fintype.card G) → N₀ ≤ Fintype.card G →
      |expIid G (k0 (Fintype.card G)).toNat (fun x => (holes x : ℝ)) /
            (((Fintype.card G : ℝ) - 1) * Real.exp (-lam0 (Fintype.card G))) - 1| ≤ ε ∧
      |expIid G (k0 (Fintype.card G)).toNat (fun x => (holes x : ℝ) * ((holes x : ℝ) - 1)) /
            (((Fintype.card G : ℝ) - 1) * ((Fintype.card G : ℝ) - 2) *
              Real.exp (-2 * lam0 (Fintype.card G))) - 1| ≤ ε ∧
      C ≤ expIid G (k0 (Fintype.card G)).toNat (fun x => (holes x : ℝ)) ∧
      (expIid G (k0 (Fintype.card G)).toNat (fun x => (holes x : ℝ) ^ 2) -
            (expIid G (k0 (Fintype.card G)).toNat (fun x => (holes x : ℝ))) ^ 2) /
          (expIid G (k0 (Fintype.card G)).toNat (fun x => (holes x : ℝ))) ^ 2 ≤ ε ∧
      1 - ε ≤ probIid G (k0 (Fintype.card G)).toNat (fun x => 0 < holes x) := by sorry

end AlgCoverage.OddOrder
