-- Prove2me | Theorems.Thm_FasterSFM_fact_3
-- name    : FasterSFM.fact_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:34:29.528238+00:00
-- url     : https://prove2.me/theorems/01692750-ab63-4f66-8346-1e6446f30d42
-- title:
--   Fact 3 — calibration facts: persistence, marginal lower bound, prefix upper bound
-- statement:
--   Let $h:2^U\to\mathbb R$ be submodular, let $D$ be the current quotient DAG with $N$ blocks, and let the witness value $m=h(\emptyset)+1-t$ satisfy $m\le h(\emptyset)$ and $m\le h(U)$. Suppose $D$ is calibrated at the parameter $t$ and let $s\ge t$. Then $D$ is calibrated at $s$, and with $c_v=H_s(A_v)$:
--
--   1. if $T$ and $T\cup\{v\}$ are closed and $v\notin T$, then
--   $$H_s(T\cup\{v\})-H_s(T)\ \ge\ -c_v;$$
--   2. if $\emptyset=T_0\subset T_1\subset\dots\subset T_N=V(D)$ are the prefixes of a descendant-first order $\pi$, then for every $j$
--   $$H_s(T_j)\ \le\ \sum_{k>j}c_{\pi(k)}\ \le\ \sum_z c_z .$$
--
--   These facts give the marginal and prefix bounds behind the no-cancellation inequality of Lemma 5.
--
--   Differences from the source:
--   - reading: the algorithm's standing setting (h(∅), h(U) ≥ m, so that H_t is submodular, p.9) → explicit hypothesis EndpointsAbove h t: h(∅) + 1 − t ≤ h(∅) and h(∅) + 1 − t ≤ h(U); reason: reading R7: the algorithm's context made explicit
--   - generalization: the quotient DAG of the implication graph (SCCs contracted) → any partition of Fin n into N nonempty blocks with an acyclic arc relation on the blocks; reason: the lemma's proof uses only these properties (reading R8); the quotient DAG is one instance
--   - encoding: the order π and its prefixes T_j → a position map σ; T_j = blocks at positions < j, Σ_{k>j} c_{π(k)} = sum over positions ≥ j; reason: Lean encoding of an ordering; same instances
--   - encoding: "calibration persists, since F ≥ 0" → the conclusion that D is calibrated at s; reason: the parenthetical claim, stated as a conjunct
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, Fact 3, pp.10–11

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_FasterSFM_BlockDAG

namespace FasterSFM

open Classical

/-- **Fact 3** (Calibration facts), pp.10–11.

Ene & Nguyen, arXiv:2610.25403v1, Fact 3, pp.10–11.

"Let D be calibrated at parameter t and let s ≥ t (calibration persists, since F ≥ 0).
(a) If T and T ∪ {v} are closed and v ∉ T, then H_s(T ∪ {v}) − H_s(T) ≥ −c_v, where now
c_v = H_s(A_v).
(b) If ∅ = T₀ ⊂ T₁ ⊂ ⋯ ⊂ T_N = V(D) are the prefixes of a descendant-first order π, then
H_s(T_j) ≤ Σ_{k>j} c_{π(k)} ≤ Σ_z c_z."

**Formalization Note.** `h` is submodular on `2^{Fin n}` and the witness value `m = h(∅) + 1 − t`
is at most `h(∅)` and `h(U)` (`EndpointsAbove h t`, the algorithm's standing fact of p.9 that makes
`H_t` submodular; reading R7). Blocks are `Fin N` for any block structure with an acyclic arc relation
(reading R8). The ordering is a position map `σ`; `T_j` is the set of blocks at positions `< j`, and
`Σ_{k>j} c_{π(k)}` is the sum over the blocks at positions `≥ j`. The persistence clause is stated as
`D` calibrated at `s`. -/
theorem fact_3 {n N : ℕ} (h : Finset (Fin n) → ℝ) (hsub : NonmonotoneSubmod.Shared.Submodular h)
    (D : BlockDAG n N) (t s : ℝ) (hend : EndpointsAbove h t) (hcal : D.Calibrated h t)
    (hts : t ≤ s) :
    D.Calibrated h s ∧
    (∀ (T : Finset (Fin N)) (v : Fin N), D.Closed T → D.Closed (insert v T) → v ∉ T →
      -D.cz h s v ≤ D.Hs h s (insert v T) - D.Hs h s T) ∧
    (∀ σ : Equiv.Perm (Fin N), D.DescendantFirst σ → ∀ j : ℕ, j ≤ N →
      D.Hs h s (prefixSet σ j) ≤
          ∑ v ∈ Finset.univ.filter (fun v => j ≤ (σ v : ℕ)), D.cz h s v ∧
        ∑ v ∈ Finset.univ.filter (fun v => j ≤ (σ v : ℕ)), D.cz h s v ≤ ∑ z, D.cz h s z) := by sorry

end FasterSFM
