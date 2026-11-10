-- Prove2me | Theorems.Thm_CNFLearnMQ_lemma_5_13
-- name    : CNFLearnMQ.lemma_5_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:17:20.237556+00:00
-- url     : https://prove2.me/theorems/20baab6f-d3d6-42fb-b1cc-b7a3ccd6c28c
-- title:
--   Lemma 5.13 — local lemma bounds on prescribed assignments and core probabilities
-- statement:
--   Let $t\ge1$ be real, $k\ge100$ and $d\ge1$ integers satisfying the local lemma condition (3), $k\ge(1+1/t)\log d+2\log k+t-3\log t+5$, and let $\Phi=(V,C)$ be an $n$-variable $(k,d)$-CNF formula with $n\ge k$ (the standing assumptions of §5, p.21, and §3, p.13).
--   Let $\rho=2^{-k}(1-2^{1-k})^{-dk}$. Then:
--
--   1. For every integer $\ell\ge1$, target clauses $c_1,\dots,c_\ell\in C$ with pairwise disjoint variable sets, and assignments $\tau_i\in\{\mathrm{True},\mathrm{False}\}^{\mathrm{vbl}(c_i)}$,
--   $$\Pr_{X\sim\mu_\Phi}\big[X_{\mathrm{vbl}(c_i)}=\tau_i\text{ for all }i\in[\ell]\big]\le\rho^\ell.$$
--   2. For every nonempty subclause $b=(B,\tau_B)$,
--   $$\Pr_{X\sim\mu_\Phi}\big[b\in\mathcal C(\mathcal R_X)\big]\le d\rho.$$
--
--   These bounds compare conditional core probabilities with their unconditional values in the weak-extension analysis.
--
--   Differences from the source:
--   - encoding: $\tau_i\in\{\mathrm{True},\mathrm{False}\}^{\mathrm{vbl}(c_i)}$ → full assignments $\tau_i$ of which only the values on $\mathrm{vbl}(c_i)$ are used; reason: every partial assignment extends to a full one; same events
--   - encoding: $\mu_\Phi$, defined when $\Omega(\Phi)\ne\emptyset$ (p.13); under (3) $\Phi$ is satisfiable by Theorem 3.1 → nonemptiness of the solution set is a hypothesis `h`; reason: the published law `solutionLaw` needs the proof; under the standing assumptions it always holds, so no instance is excluded
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Lemma 5.13, pp.29–30

import Mathlib
import Definitions.Def_CNFLearnMQ_Success

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant

/-- Lemma 5.13, pp.29–30 (Feng, Yu, Zhang, *Learning CNF Formulas with Uniform Random Solutions and Membership Queries*, STOC 2027 submission (manuscript sha256 519ee6d4…)). Under the standing assumptions of §5, with
`ρ = 2^{−k}(1 − 2^{1−k})^{−dk}`:
1. for every `ℓ ≥ 1`, target clauses `c_1, …, c_ℓ ∈ C` with pairwise disjoint variable sets and
   assignments `τ_i` of `vbl(c_i)`, `P_{X∼µ_Φ}[X_{vbl(c_i)} = τ_i for all i] ≤ ρ^ℓ`;
2. for every nonempty subclause `b = (B, τ_B)`, `P_{X∼µ_Φ}[b ∈ C(R_X)] ≤ dρ`.

**Formalization Note** `τ_i` is given as a full assignment of which only the values on `vbl(c_i)`
matter. `µ_Φ` is the published `solutionLaw`; it exists only when `Ω(Φ) ≠ ∅`, so nonemptiness is a
hypothesis (it always holds under (3), Theorem 3.1). -/
theorem lemma_5_13 {n k d : ℕ} {t : ℝ} (ht : 1 ≤ t) (hk : 100 ≤ k) (hd : 1 ≤ d) (hLLL : LLLCondition k d t) (hn : k ≤ n)
    (Φ : CNF n) (hΦ : KD Φ k d) (h : (solutions Φ).Nonempty) :
    (∀ ℓ : ℕ, 1 ≤ ℓ → ∀ cs : Fin ℓ → Clause n, (∀ i, cs i ∈ Φ) →
      (∀ i j, i ≠ j → Disjoint (support (cs i)) (support (cs j))) →
      ∀ τ : Fin ℓ → Assignment n,
        eventProb (solutionLaw Φ h) (fun X => ∀ i, ∀ v ∈ support (cs i), X v = τ i v) ≤
          rho k d ^ ℓ) ∧
    (∀ b : Clause n, (support b).Nonempty →
      eventProb (solutionLaw Φ h) (fun X => b ∈ inducedFamily X (cores Φ X)) ≤
        d * rho k d) := by sorry

end CNFLearnMQ
