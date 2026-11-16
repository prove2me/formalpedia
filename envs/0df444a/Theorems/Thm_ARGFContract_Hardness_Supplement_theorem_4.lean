-- Prove2me | Theorems.Thm_ARGFContract_Hardness_Supplement_theorem_4
-- name    : ARGFContract.Hardness.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:04:41.318971+00:00
-- url     : https://prove2.me/theorems/51635721-57e5-45b4-b7a3-2003a59fc7b0
-- title:
--   Theorem 4 (companion theorem; not used in the proof of the goal) — Instance-dependent factor α(Γ) of the minimum-cost-prefix algorithm
-- statement:
--   Let $N\ge1$ agents have competencies $p_i\in\mathbb R$ and costs $c_i\ge0$, let $f$ be an ARGF whose evaluation on an $m$-set takes at most $D(m+1)^{K_f}$ time, and let $S_c^n$ be the $n$ cheapest agents, $\mathrm{Top}_n(p)$ the $n$ most competent ones, and
--
--   $$D=\max_{1\le n\le N}\mu(S_c^n),\qquad U=\max_{1\le n\le N}\Big(f(\mathrm{Top}_n(p))-\sum_{i\in S_c^n}c_i\Big),\qquad \alpha(\Gamma)=\frac UD\quad(3.12).$$
--
--   In the nontrivial regime $D>0$ of the proof, there are an absolute exponent $d$ and one program which, for every $K_f$ and $D$, with a constant $C$ depending only on them, computes in time $C(N+1)^{d+K_f}$:
--
--   1. a committee $\hat S_{OPT}=S_c^{\hat n}$ with $\mu(\hat S_{OPT})=D$, as in (3.14);
--   2. the number $\alpha(\Gamma)$, which satisfies $\alpha(\Gamma)\ge1$;
--
--   and for every $\alpha\ge\alpha(\Gamma)$,
--
--   $$\max_{S\subseteq E}\mu(S)\ \le\ \alpha\,\mu(\hat S_{OPT}) .$$
--
--   The factor is instance dependent: it is computed from the costs, the competencies and the oracle, and no uniform bound across instances is claimed.
--
--   **Formalization Note** Running time is measured in the value-oracle real RAM of `OracleMachine`. The minimum-cost and top-competency prefixes break ties by agent index. The case $D\le0$ is outside the statement, as it is outside the ratio formula (3.12).
--
--   Differences from the source:
--   - encoding: running time of an offline algorithm with value oracle f (Definition 2.1(3): an evaluation costs O(|S|^{K_f})) → one uniform admissible program of the value-oracle real RAM (published SmaleNinth core plus integer memory, one-agent committee edits and a query instruction); time = executed instructions plus the oracle time τ(|S|) of every query; reason: unit-cost real arithmetic and comparisons with no sort, maximum or set-scan primitive; the oracle is charged per query as in Definition 2.1(3)
--   - reading: the nontrivial case µ(S_c^n) > 0 in which the proof computes the ratio (pp. 20–21) → hypotheses N ≥ 1 and D = max_{1≤n≤N} µ(S_c^n) > 0; reason: (3.12) is a ratio only there; the source gives no extension to D ≤ 0
--   - reading: α is a polynomial-time function of Γ = (C, P), bounded by (3.10)/(3.13) → the program outputs exactly α(Γ) = U/D of (3.12), computed with oracle calls to f; reason: the proof evaluates f(Top_n(p)) to obtain α(Γ); (3.10) and (3.13) divide by a set and are malformed, (3.12) is the well-formed formula
--   - reading: Definition 3.3: an approximation factor is ≥ 1 → conclusion 1 ≤ α(Γ); reason: the factor convention of Definition 3.3; it follows from the source's bounds U ≥ OPT ≥ D
--   - encoding: polynomial time → C·(N+1)^{d+K_f} with an absolute d and C depending only on K_f and D (τ(m) ≤ D(m+1)^{K_f}); reason: polynomial in N for a polynomial-time oracle, constants fixed before N
--   - encoding: Ŝ_OPT = argmax_n µ(S_c^n) (3.14), S_c^n a minimum-cost n-set → the output is S_c^k for some 1 ≤ k ≤ N with µ(S_c^k) = D; S_c^k the k cheapest agents with ties by index; reason: a cost-sorted list fixes one cheapest k-set; any maximizing k is allowed
--   - generalization: E is the pruned ground set returned by Algorithm 1 (p. 10, 'throughout the remainder of the paper') → no pruning hypothesis (p_i − c_i > 0 is not assumed); reason: the statement holds on every ground set; the pruned instances are a special case
-- source:
--   Jalal Etesami, Larkin Liu, Rilind Sahitaj, STOC 2027 submission #348 (October 2026), Theorem 4, p. 20 (proof pp. 20–22)

import Mathlib
import Definitions.Def_ARGFContract_Hardness_ARGF
import Definitions.Def_ARGFContract_Hardness_Supplement_Prefixes
import Definitions.Def_ARGFContract_Hardness_Supplement_OracleMachine

open Finset

namespace ARGFContract.Hardness.Supplement

/-- Theorem 4, pp. 20–22, in the nontrivial regime `D = max_{1≤k≤N} µ(S_c^k) > 0` of its
proof. One uniform program, given costs and competencies, computes in polynomial time
`C (N+1)^(d + K_f)` (oracle cost at most `D (m+1)^{K_f}` on an `m`-set) a minimum-cost prefix
`Ŝ_OPT = S_c^k` attaining `D` (3.14) and the exact factor `α(Γ) = U / D` of (3.12); then
`α(Γ) ≥ 1` and `µ(S_OPT) ≤ α µ(Ŝ_OPT)` for every `α ≥ α(Γ)`. -/
theorem theorem_4 :
    ∃ P : OracleProgram, Admissible P ∧ ∃ d : ℕ, ∀ Kf Dτ : ℕ, ∃ C : ℕ,
      ∀ (n : ℕ) (hn : 0 < n) (p c : Fin n → ℝ) (f : Finset (Fin n) → ℝ) (τ : ℕ → ℕ),
        ARGFContract.Hardness.IsARGF p f → (∀ i, 0 ≤ c i) →
        (∀ m, τ m ≤ Dτ * (m + 1) ^ Kf) →
        0 < minCostCandidateValue hn f c →
        RunsWithin P f τ (initState n (encodeReals c p) (encodeInts (n := n) 0 (fun _ => 0)))
          (C * (n + 1) ^ (d + Kf))
          (fun S a _ =>
            (∃ k ∈ Icc 1 n, S = bottomSet c k) ∧
            netUtilityReal f c S = minCostCandidateValue hn f c ∧
            a = alphaGamma hn f p c ∧ 1 ≤ a ∧
            ∀ α : ℝ, alphaGamma hn f p c ≤ α →
              maxNetUtilityReal f c ≤ α * netUtilityReal f c S) := by sorry

end ARGFContract.Hardness.Supplement
