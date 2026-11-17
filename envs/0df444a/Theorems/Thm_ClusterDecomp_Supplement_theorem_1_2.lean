-- Prove2me | Theorems.Thm_ClusterDecomp_Supplement_theorem_1_2
-- name    : ClusterDecomp.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:59:21.481241+00:00
-- url     : https://prove2.me/theorems/010825d2-9b57-4bbc-a33c-02eb139600fb
-- title:
--   Theorem 1.2 — approximation boost from $\alpha$ to $1+\varepsilon$
-- statement:
--   Let $G$ be a finite weighted graph in which every vertex has positive degree. Fix $\varepsilon>0$, $\alpha\ge1$ and $2\le k<|V(G)|$, with $\rho_G(k)>0$. Let $B_1,\ldots,B_k$ be pairwise disjoint positive-volume sets satisfying
--
--   $$
--   \max_i\phi_G(B_i)\le\alpha\rho_G(k).
--   $$
--
--   If
--
--   $$
--   \rho_G(k+1)\ge \frac{18(\alpha+1)(1+\varepsilon)}{\varepsilon}\,\rho_G(k),
--   $$
--
--   then every run of Algorithm 3 returns pairwise disjoint positive-volume sets $C_1,\ldots,C_k$ such that
--
--   $$
--   \max_i\phi_G(C_i)\le(1+\varepsilon)\rho_G(k).
--   $$
--
--   There is an absolute constant $C>0$ such that the run makes at most $Ck(1+\log\alpha)$ minimum $s$-$t$ cut computations. Thus the procedure boosts any $\alpha$-approximate family to a $(1+\varepsilon)$-approximate family under the stated higher-order conductance gap.
--
--   Differences from the source:
--   - generalization: the section's integer weights with polynomial max/min ratio → arbitrary symmetric nonnegative real weights with positive degrees; reason: Algorithm 3 and the proof of Theorem 1.2 use neither integrality nor the ratio bound, and every source instance is included
--   - encoding: the quotient inequality for $\rho_G(k+1)/\rho_G(k)$ → the equivalent multiplicative inequality in $\mathbb R_{\ge0}\cup\{+\infty\}$; reason: $\rho_G(k)>0$ and $k<|V|$ make the source quotient meaningful, while the multiplicative form avoids extended-real division and never maps $+\infty$ to zero
--   - encoding: Algorithm 3 with an unspecified minimum-cut tie-break → every relational run, with the call count stored in that run and one absolute big-O constant quantified before all inputs; reason: this is the tie-break-independent and quantifier-explicit reading of the algorithm and $O(k(1+\log\alpha))$
--   - encoding: nonempty output sets → positive-volume output sets; reason: under the retained positive-degree assumption these conditions are equivalent
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), Theorem 1.2 p.3 (PDF p.5), Algorithm 3 pp.19–20 (PDF pp.21–22)

import Mathlib
import Definitions.Def_ClusterDecomp_Supplement_Alg3Run

open Finset
open scoped ENNReal

namespace ClusterDecomp.Supplement

open ClusterDecomp

/-- **Theorem 1.2 (approximation boost).**

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027
submission (manuscript sha256 ba091f54…), Theorem 1.2, p.3 (PDF p.5), with Algorithm 3 on
pp.19–20 (PDF pp.21–22).

Let `G` have positive degrees, let `ε > 0`, `α ≥ 1`, `2 ≤ k < |V|`, and `ρ_G(k) > 0`, and
let the `B_i` be pairwise disjoint positive-volume sets satisfying
`max_i ϕ_G(B_i) ≤ α ρ_G(k)`. If

`18(α+1)(1+ε)/ε · ρ_G(k) ≤ ρ_G(k+1)`,

then every run of Algorithm 3 returns pairwise disjoint positive-volume sets `C_i` with
`max_i ϕ_G(C_i) ≤ (1+ε)ρ_G(k)`, using at most `C k (1 + log α)` minimum `s`-`t` cut
computations for one universal constant `C > 0`.

**Formalization Note.**
* The paper's standing assumption that every vertex has positive degree is retained. Its integral-weight
  and polynomial weight-ratio assumptions are omitted: neither Algorithm 3 nor the proof of Theorem 1.2
  uses them, so this is a genuine generalization to the paper's real weighted graph model.
* `ρ` is `ℝ≥0∞`-valued. The approximation and gap hypotheses are written multiplicatively, without
  division in `ℝ≥0∞` and without applying `.toReal` (which would send `⊤` to `0`).
* `Alg3Run` ranges over every possible minimum-cut output in every call. Thus the universal quantifier
  over `run` states the guarantee for every tie-break, as the unspecified minimum-cut instruction in
  Algorithm 3 requires.
* The existential cut-count constant precedes the graph, `k`, `α`, `ε`, the input family and the run;
  it is therefore an absolute big-O constant. Positive volume in the conclusion is equivalent to the
  printed nonemptiness because every vertex has positive degree. -/
theorem theorem_1_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V), G.PosDeg →
        ∀ (k : ℕ) (ε α : ℝ) (B : Fin k → Finset V),
          2 ≤ k → k < Fintype.card V → 0 < ε → 1 ≤ α → 0 < G.rho k →
          (Pairwise fun i j => Disjoint (B i) (B j)) →
          (∀ i, 0 < G.vol (B i)) →
          (∀ i, ENNReal.ofReal (G.phiOut (B i)) ≤ ENNReal.ofReal α * G.rho k) →
          ENNReal.ofReal (18 * (α + 1) * (1 + ε) / ε) * G.rho k ≤ G.rho (k + 1) →
          Nonempty (Alg3Run G k B α) ∧
            ∀ run : Alg3Run G k B α,
              ((run.calls.length : ℕ) : ℝ) ≤ C * (k : ℝ) * (1 + Real.log α) ∧
              ∃ D : Fin k → Finset V, run.output = some D ∧
                (Pairwise fun i j => Disjoint (D i) (D j)) ∧
                ∀ i, 0 < G.vol (D i) ∧
                  ENNReal.ofReal (G.phiOut (D i)) ≤ ENNReal.ofReal (1 + ε) * G.rho k := by sorry

end ClusterDecomp.Supplement
