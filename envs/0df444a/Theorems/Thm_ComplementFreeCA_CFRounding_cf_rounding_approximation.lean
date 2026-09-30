-- Prove2me | Theorems.Thm_ComplementFreeCA_CFRounding_cf_rounding_approximation
-- name    : ComplementFreeCA.CFRounding.cf_rounding_approximation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:18:54.004374+00:00
-- url     : https://prove2.me/theorems/706811c4-44ae-4be9-9159-f87fea6f3288
-- title:
--   Theorem 3.1 — the LP-rounding-and-splitting algorithm is a 3k-approximation, k = ⌊3 log m / log log m⌋, for complement-free bidders
-- statement:
--   There is $m_0$ such that the following holds for every number of items $m\ge m_0$ and every number of bidders $n$. Let $v_1,\dots,v_n$ be normalized, monotone, complement-free valuations, let $x$ be an optimal solution of the LP relaxation with value $OPT^*$, and let $k=\lfloor 3\log m/\log\log m\rfloor$. Write $OPT$ for the welfare of any allocation $(O_1,\dots,O_n)$.
--
--   1. **Step (i) succeeds.** If $OPT^*>3\max_i v_i(M)$, then with probability greater than $1/6$ the randomized-rounding preallocation $(S_1,\dots,S_n)$ satisfies both: every item appears in at most $k$ of the $S_i$, and $\sum_i v_i(S_i)\ge OPT^*/3$.
--   2. **The guarantee.** For every preallocation $(S_1,\dots,S_n)$ with these two properties, every best layer $r$ of step (iii), and every admissible bidder of step (iv), the algorithm's output is an allocation, and its welfare $W$ satisfies
--   $$W\ \ge\ \frac{\sum_i v_i(O_i)}{3k}\qquad\text{for every allocation } (O_1,\dots,O_n).$$
--   3. **The small case.** If $OPT^*\le 3\max_i v_i(M)$, then giving all of $M$ to a bidder $i_0$ maximizing $v_i(M)$ has welfare $v_{i_0}(M)\ge\sum_i v_i(O_i)/3$ for every allocation $(O_i)$.
--
--   This is Theorem 3.1 of the paper: for complement-free bidders the algorithm produces an allocation that is an $O(\log m/\log\log m)$-approximation to the optimal one.
--
--   **Formalization Note** The paper writes $O(k)=O(\log m/\log\log m)$; its proof yields the explicit ratio $3k$ with $k=\lfloor3\log m/\log\log m\rfloor$ (natural logarithm), for $m\ge m_0$, and $m_0$ is existential because Lemma 3.1 holds for sufficiently large $m$. The paper's w.l.o.g. scaling $\max_i v_i(M)=1$ with the case split $OPT^*\le3$ / $OPT^*>3$ is replaced by the scale-free split $OPT^*\le 3\max_i v_i(M)$ / $OPT^*>3\max_i v_i(M)$, written as $3v_i(M)<OPT^*$ for all $i$. Step (i) is a randomized search; part 1 is the success probability of one rounding, and the probability is the finite-sum rounding law of the LP definition file. The choices of $r$ in step (iii) and of the bidder in step (iv) are left open by the paper and are universally quantified. Running time is not modeled.
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 5, Theorem 3.1 (algorithm steps (i)–(iv), p. 5; proof and §3.1.1, p. 6)

import Mathlib
import Definitions.Def_ComplementFreeCA_CFRounding_Auction
import Definitions.Def_ComplementFreeCA_CFRounding_LP
import Definitions.Def_ComplementFreeCA_CFRounding_Algorithm

namespace ComplementFreeCA.CFRounding

theorem cf_rounding_approximation :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (n : ℕ) (v : Fin n → Finset (Fin m) → ℝ),
      (∀ i, IsNormalized (v i)) → (∀ i, IsMonotone (v i)) → (∀ i, IsSubadditive (v i)) →
      ∀ x : Fin n → Finset (Fin m) → ℝ, IsOptimalLP v x →
        -- (a) step (i) succeeds with probability greater than 1/6
        ((∀ i, 3 * v i Finset.univ < lpValue v x) →
          1 / 6 < roundProb x
            (fun σ => (∀ j, count σ j ≤ kOf m) ∧ lpValue v x / 3 ≤ welfare v σ)) ∧
        -- (b) from any such preallocation, every admissible run of steps (ii)–(iv) outputs
        --     an allocation whose welfare is at least OPT / (3k)
        (∀ σ : Fin n → Finset (Fin m), (∀ j, count σ j ≤ kOf m) →
          lpValue v x / 3 ≤ welfare v σ →
          ∀ r : ℕ, IsBestLayer v σ (kOf m) r →
          ∀ i₀ : Fin n, IsStepFourChoice v (fun i => layer σ i r) i₀ →
            IsAllocation (algOutput v σ r i₀) ∧
            ∀ O : Fin n → Finset (Fin m), IsAllocation O →
              welfare v O / (3 * kOf m) ≤ welfare v (algOutput v σ r i₀)) ∧
        -- (c) the small case: giving all items to a bidder maximizing vᵢ(M) is a
        --     3-approximation
        (∀ i₀ : Fin n, (∀ i, v i Finset.univ ≤ v i₀ Finset.univ) →
          lpValue v x ≤ 3 * v i₀ Finset.univ →
          ∀ O : Fin n → Finset (Fin m), IsAllocation O → welfare v O / 3 ≤ v i₀ Finset.univ) := by sorry

end ComplementFreeCA.CFRounding
