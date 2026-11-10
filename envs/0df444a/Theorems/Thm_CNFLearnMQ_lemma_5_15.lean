-- Prove2me | Theorems.Thm_CNFLearnMQ_lemma_5_15
-- name    : CNFLearnMQ.lemma_5_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:18:02.803047+00:00
-- url     : https://prove2.me/theorems/ae33ccb2-2bb6-4020-8cb1-7704efaa11fb
-- title:
--   Lemma 5.15 — at most $2^{8dk^2}\ln(1/\eta)$ subclauses with large conditional core probability
-- statement:
--   Let $t\ge1$ be real, $k\ge100$ and $d\ge1$ integers satisfying the local lemma condition (3), $k\ge(1+1/t)\log d+2\log k+t-3\log t+5$, and let $\Phi=(V,C)$ be an $n$-variable $(k,d)$-CNF formula with $n\ge k$ (the standing assumptions of §5, p.21, and §3, p.13).
--   Let $0<\eta\le e^{-1}$ and let $s=(S,\sigma_S)$ be a subclause with $q_s\ge\eta$. Let $B_s$ be the set of subclauses $b=(B,\tau_B)$ with $S\cap B=\emptyset$, $|S|+|B|\le k$ and $q_s(b)\ge d\rho+\phi$. Then
--   $$|B_s|\le\phi^{-4}\ln(1/\eta)=2^{8dk^2}\ln(1/\eta).$$
--
--   This caps the number of weak children of a node of the extension forest (Lemma 5.11).
--
--   Differences from the source:
--   - generalization: $\eta=\varepsilon/(3N_{\mathrm{tot}})$ of (7) → every $\eta\in(0,e^{-1}]$; reason: the proof uses only $\ln(1/q_s)\le\ln(1/\eta)$ and $\ln(1/\eta)\ge1$ (p.32); the parameter of (7) is at most $1/3<e^{-1}$
--   - encoding: $q_s(b)$, the conditional probability given $X_S=\sigma_S$ → `qcond`, the joint probability divided by $q_s$; reason: equal when $q_s>0$, which holds since $q_s\ge\eta>0$
--   - encoding: $\mu_\Phi$, defined when $\Omega(\Phi)\ne\emptyset$ (p.13); under (3) $\Phi$ is satisfiable by Theorem 3.1 → nonemptiness of the solution set is a hypothesis `h`; reason: the published law `solutionLaw` needs the proof; under the standing assumptions it always holds, so no instance is excluded
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Lemma 5.15, p.31

import Mathlib
import Definitions.Def_CNFLearnMQ_Success

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant

/-- Lemma 5.15, p.31 (Feng, Yu, Zhang, *Learning CNF Formulas with Uniform Random Solutions and Membership Queries*, STOC 2027 submission (manuscript sha256 519ee6d4…)). Under the standing assumptions of §5, let `0 < η ≤ e^{−1}` and let
`s = (S, σ_S)` be a subclause with `q_s ≥ η`. Let `B_s` be the set of subclauses `b = (B, τ_B)` with
`S ∩ B = ∅`, `|S| + |B| ≤ k` and `q_s(b) ≥ dρ + ϕ`. Then
`|B_s| ≤ ϕ^{−4} ln(1/η) = 2^{8dk²} ln(1/η)`.

**Formalization Note** The paper takes `η` to be the parameter `ε/(3N_tot)` of (7), which satisfies
`η ≤ 1/3 < e^{−1}`; the statement here holds for every `η ∈ (0, e^{−1}]` (the proof uses only
`ln(1/q_s) ≤ ln(1/η)` and `ln(1/η) ≥ 1`, p.32). `q_s(b)` is the conditional probability `qcond`,
well defined since `q_s ≥ η > 0`. -/
theorem lemma_5_15 {n k d : ℕ} {t : ℝ} (ht : 1 ≤ t) (hk : 100 ≤ k) (hd : 1 ≤ d) (hLLL : LLLCondition k d t) (hn : k ≤ n)
    (Φ : CNF n) (hΦ : KD Φ k d) (h : (solutions Φ).Nonempty) (η : ℝ) (hη0 : 0 < η)
    (hη1 : η ≤ Real.exp (-1)) (s : Clause n) (hqs : η ≤ q Φ h s) :
    (((Finset.univ.filter fun b : Clause n => Disjoint (support s) (support b) ∧
        width s + width b ≤ k ∧ (d : ℝ) * rho k d + phi d k ≤ qcond Φ h s b).card : ℝ) ≤
      (phi d k)⁻¹ ^ 4 * Real.log (1 / η)) ∧
    (phi d k)⁻¹ ^ 4 * Real.log (1 / η) = (2 : ℝ) ^ (8 * d * k ^ 2) * Real.log (1 / η) := by sorry

end CNFLearnMQ
