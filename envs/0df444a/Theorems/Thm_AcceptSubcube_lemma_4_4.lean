-- Prove2me | Theorems.Thm_AcceptSubcube_lemma_4_4
-- name    : AcceptSubcube.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:06.395192+00:00
-- url     : https://prove2.me/theorems/5bcb7baa-604c-460f-9e3e-b6f993cc5619
-- title:
--   Lemma 4.4 — the charging interface
-- statement:
--   Let $k\ge3$, $D=D_3(n)$, $M=\binom nk$, and let $\mathcal I$ be a $k$-uniform instance with at most one predicate per scope, already shifted so that the center is $0^n$. From any rational feasible point of the relaxation (10) with radius $r$, of objective $L$ and active set $U$, $s=|U|$, one can construct in polynomial time a weighted CNF $\Phi_U$ with:
--
--   1. unary and binary clauses on variables in $U$, with nonnegative integer weights of total at most $4M$;
--   2. fractional cost $V\le 8L$;
--   3. for every $z\in\{0,1\}^U$ that makes every literal $u$ with $\mathbb P[u=1]<1/4$ false (the bias condition), the completion $\hat x$ of $z$ by zeros outside $U$ satisfies
--   $$C_{\mathcal I}(\hat x)\le C_{\Phi_U}(z)+2L+D\binom s3+8Dr\binom s2;$$
--   4. $D\binom s3+8Dr\binom s2\le K'_k D r^3$ for a constant $K'_k$ depending only on $k$.
--
--   The interface reduces cubic repair to rounding a Min-2-CNF Deletion instance under a bias condition.
--
--   Differences from the source:
--   - encoding: a feasible point of the relaxation of §4.3 for the instance XORed with τ → a rational moment list satisfying RelaxFeasible k n r, for every instance (playing the role of the shifted one); reason: every shifted instance is an instance; moments parametrize the consistent local laws (proof of Lemma 4.7)
--   - reading: construct in polynomial time → a TM2 polynomial-time map (I, r, point) ↦ Φ_U, the polynomial depending on k; reason: the paper names no machine model; k is fixed
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Lemma 4.4, p.18 (setting: §4.3, p.17)

import Mathlib
import Definitions.Def_OnlineCRS_Combine_Sym
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost
import Definitions.Def_AcceptSubcube_RelaxFeasible
import Definitions.Def_AcceptSubcube_WCNF
import Definitions.Def_AcceptSubcube_encInst

namespace AcceptSubcube

/-- **Lemma 4.4 (Charging interface).**

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Lemma 4.4, p.18: "From any feasible point one
can construct in polynomial time a nonnegative integer-weighted unary/binary CNF Φ_U on U of
fractional cost V ≤ 8L with the following property. If z ∈ {0,1}^U makes every literal u with
P[u = 1] < 1/4 false (the bias condition), then its completion x̂ by zeros outside U satisfies
C_I(x̂) ≤ C_{Φ_U}(z) + 2L + D (s choose 3) + 8Dr (s choose 2). (11) The last two terms are at most
K′_k D r³, and the weights total at most 4M."

For every `k ≥ 3` there are a constant `K′` and a polynomial-time map from `(I, r, point)` to a CNF
`Φ` with: unary/binary clauses, nonnegative integer weights, variables in `U`; `V ≤ 8L`; (11) for
every `z` with the bias condition; `D (s choose 3) + 8Dr (s choose 2) ≤ K′ D r³`; total weight
`≤ 4M`.

**Formalization Note.** §4's setting (pp.15, 17): `k ≥ 3`, `D = D₃(n)`, `M = (n choose k)`, the
instance arbitrary (well formed, `k`-uniform, at most one predicate per scope) and already shifted
so that the center is `0^n`; "feasible point" = a rational point (moment list) of the relaxation (10)
with radius `r` (`RelaxFeasible`; no semidefinite constraint). `U` and `s = |U|` are those of (8)
(`activeSet`). `L` is the objective `relaxObj`, `V` the fractional cost under the point's laws. `z`
is read only on `U`, and the bias condition ranges over both literals of every active variable. -/
theorem lemma_4_4 (k : ℕ) (hk : 3 ≤ k) :
    ∃ (K' : ℝ) (Phi : GInst × ℕ × List (List ℕ × ℚ) → List (ℚ × List (ℕ × Bool))),
      Nonempty (Turing.TM2ComputableInPolyTime encChargeIn encCNF Phi) ∧
      ∀ I : GInst, I.WellFormed → I.Uniform k → I.ScopeUnique →
        ∀ (r : ℕ) (L : List (List ℕ × ℚ)), RelaxFeasible k I.n r L →
          IsUnaryBinary (Phi (I, r, L)) ∧ NatWeights (Phi (I, r, L)) ∧
          OnVars (Phi (I, r, L)) (activeSet k I.n L) ∧
          fracCost L (Phi (I, r, L)) ≤ 8 * relaxObj I L ∧
          (∀ z : ℕ → Bool,
              (∀ i ∈ activeSet k I.n L, ∀ b : Bool, lit1 L i b < 1 / 4 → z i ≠ b) →
              (cost I (fun i => decide ((i : ℕ) ∈ activeSet k I.n L) && z i) : ℚ) ≤
                cnfCost (Phi (I, r, L)) z + 2 * relaxObj I L +
                  (Dj k 3 I.n : ℚ) * ((activeSet k I.n L).card.choose 3 : ℚ) +
                  8 * (Dj k 3 I.n : ℚ) * (r : ℚ) * ((activeSet k I.n L).card.choose 2 : ℚ)) ∧
          (Dj k 3 I.n : ℝ) * ((activeSet k I.n L).card.choose 3 : ℝ) +
              8 * (Dj k 3 I.n : ℝ) * (r : ℝ) * ((activeSet k I.n L).card.choose 2 : ℝ) ≤
            K' * (Dj k 3 I.n : ℝ) * (r : ℝ) ^ 3 ∧
          ((Phi (I, r, L)).map Prod.fst).sum ≤ 4 * (I.n.choose k : ℚ) := by sorry

end AcceptSubcube
