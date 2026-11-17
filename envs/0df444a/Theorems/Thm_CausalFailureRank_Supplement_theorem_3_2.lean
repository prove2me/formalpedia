-- Prove2me | Theorems.Thm_CausalFailureRank_Supplement_theorem_3_2
-- name    : CausalFailureRank.Supplement.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:52:37.361212+00:00
-- url     : https://prove2.me/theorems/508a8a3a-b2c5-4014-8511-ea5eb8ab5aa2
-- title:
--   Theorem 3.2 — common-tree safety representation
-- statement:
--   Consider the current-window tool game with known stage order and a laminar compatibility family. If $q>0$, augment the distinct nonempty compatibility sets by $U$ and every singleton to obtain one inclusion tree $\mathcal L$ with $t\le N+q+1$ nodes. For every suffix $1\le i\le N+1$ and budget $0\le k\le q+1$, the safety family is either `VOID` or $\mathcal I(b_{i,k})$ for a normalized integer capacity vector on this same tree, and
--
--   $$
--   D\in\mathcal I_{i,k}\quad\Longleftrightarrow\quad \rho(i,U\setminus D)>k.
--   $$
--
--   The table recovers $\rho(i,R)$ for every $R\subseteq U$. At every nonterminal stage with $S_i\cap R\ne\emptyset$, it returns an actual compatible tool attaining
--
--   $$
--   \max_{r\in S_i\cap R}\rho(i+1,R\setminus\{r\}).
--   $$
--
--   Uniform constants bound preprocessing by $O((N+1)(q+1)t)$ elementary integer operations, storage by $O((N+1)(q+1)t\log(q+2))$ bits, and either query by $O((q+1)t)$ operations. Capacities and counts lie in $[0,q]$; for $N,q\ge1$ these become $O(Nqt)$ and $O(qt)$. Constructing the tree and checking laminarity from incidence input uses $O((N+q+1)^2q)$ set-membership operations. If $q=0$, no tree is needed: the rank is $1$ while a stage remains and $\infty$ at termination.
--
--   This is a compact exact representation of the adaptive causal allocation game, not offline matchability.
--
--   Differences from the source:
--   - encoding: stages $1,\ldots,N+1$, budgets $0,\ldots,q+1$, nonnegative integer capacities, and the separate symbol `VOID` → 0-based `Fin (N+1)`/`Fin (q+2)`, natural-valued capacities, and `Option.none`; reason: these are bijective Lean encodings, and `none` remains distinct from the zero capacity vector
--   - encoding: a capacity vector indexed only by nodes $T\in\mathcal L$ → a total function on finite tool sets whose values are constrained and read only on $\mathcal L$; reason: coordinates outside the finite node set are ignored, so this represents exactly the same node-indexed data
--   - encoding: asymptotic operation/storage bounds written with $O(\cdot)$ → positive universal constants quantified before all game parameters and explicit inequalities; reason: this is the literal uniform meaning of the displayed complexity bounds
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), Theorem 3.2, p.8 (PDF p.9)

import Mathlib
import Definitions.Def_CausalFailureRank_Supplement_safetyTable

set_option autoImplicit false

namespace CausalFailureRank
namespace Supplement

/-- **Theorem 3.2 (Common-tree safety representation).** Zang, Li, Jin, Xu, *Causal
Failure Rank Determines Statistical Depth*, preprint (STOC 2027 submission, version of
2026-11-03, sha256 721c8b0d…), Theorem 3.2, p.8 (PDF p.9).

For every known-order laminar current-window tool game with at least one tool, one augmented
inclusion tree represents every suffix safety family and every budget `0,…,q+1`. Membership is
exactly the causal allocation game, the table recovers every rank and an actual compatible
maximizing tool, and its capacities, storage, preprocessing, query, and incidence-input tree
construction satisfy the printed bounds. The zero-tool boundary is included.

**Formalization Note.** Stages are 0-based. `none` is `VOID`, whereas `some 0` represents a family
containing the empty used set. The four constants precede every game parameter, so all `O(·)`
bounds are uniform. Operation counts are the elementary integer and set-membership work units of
the paper. The rank is the published adaptive causal game rank (`∃` one causal allocator, `∀`
future patterns), not offline matchability. -/
theorem theorem_3_2 :
    ∃ Cpre Cstore Cquery Ctree : ℕ,
      0 < Cpre ∧ 0 < Cstore ∧ 0 < Cquery ∧ 0 < Ctree ∧
      ∀ (N q : ℕ) (S : Fin N → Finset (Fin q)), IsLaminar S →
        (0 < q → ∃ T : SafetyTable S,
          T.Correct ∧
          T.tree.card ≤ N + q + 1 ∧
          T.preprocessOps ≤ Cpre * (N + 1) * (q + 1) * T.tree.card ∧
          T.storageBits ≤
            Cstore * (N + 1) * (q + 1) * T.tree.card * Nat.log2 (q + 2) ∧
          (∀ i R, T.rankQueryOps i R ≤ Cquery * (q + 1) * T.tree.card) ∧
          (∀ i R, T.toolQueryOps i R ≤ Cquery * (q + 1) * T.tree.card) ∧
          T.treeConstructionOps ≤ Ctree * (N + q + 1) ^ 2 * q ∧
          (0 < N →
            T.preprocessOps ≤ 4 * Cpre * N * q * T.tree.card ∧
            (∀ i R, T.rankQueryOps i R ≤ 2 * Cquery * q * T.tree.card) ∧
            ∀ i R, T.toolQueryOps i R ≤ 2 * Cquery * q * T.tree.card)) ∧
        (q = 0 →
          (∀ i R, i < N → gameRank S i R = 1) ∧
          ∀ i R, N ≤ i → gameRank S i R = ⊤) := by sorry

end Supplement
end CausalFailureRank
