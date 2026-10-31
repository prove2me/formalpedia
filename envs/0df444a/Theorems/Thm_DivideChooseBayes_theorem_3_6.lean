-- Prove2me | Theorems.Thm_DivideChooseBayes_theorem_3_6
-- name    : DivideChooseBayes.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:31:12.486136+00:00
-- url     : https://prove2.me/theorems/9bbf2219-c1dc-4dca-b39e-cd13b631d73c
-- title:
--   Theorem 3.6 — for $g^D \ge 0$, Algorithm 1 with $\gamma = (\varepsilon/2)\sum_i g^D_i$ is an FPTAS
-- statement:
--   Let the chooser's values be independent with $g^C_i\sim\mathcal N(\mu_i,\sigma_i^2)$, $\sigma_i>0$, let the divider's values satisfy $g^D_i\ge 0$ for all $i$, not all zero, and let $\varepsilon>0$. Run Algorithm 1 with
--
--   $$\gamma := \frac{\varepsilon}{2}\sum_{i=1}^n g^D_i .$$
--
--   1. The main loop runs exactly $\lceil 1/\varepsilon\rceil$ times.
--   2. On each iteration $k$, the program $\mathcal C_{P_k}$ in the $n$ variables $q$ has a nonempty, compact, convex feasible set and an affine objective, and attains its maximum.
--   3. For every choice of optimal solutions of these programs, the output $p$ is a division, $p\in[0,1]^n$, and
--   $$\mathbb E[u^D(p)]\ \ge\ (1-\varepsilon)\,\mathbb E[u^D(q')]\qquad\text{for every division } q' .$$
--
--   Together: Algorithm 1 is a fully polynomial-time approximation scheme for the divider's optimal interim expected utility $u^*$; the number of convex programs it solves depends on $1/\varepsilon$ only, and its value is at least $(1-\varepsilon)u^*$.
--
--   Differences from the source:
--   - reading: a fully polynomial-time approximation scheme: running time polynomial in n and 1/ε → clauses 1–2: exactly ⌈1/ε⌉ iterations, each a convex program in n variables (nonempty compact convex feasible set, affine objective, attained maximum); reason: the algorithm has real inputs, evaluates Φ⁻¹ and asks for exact optima of a second-order-cone program, so no Turing-machine reading exists; this is what the proofs of Lemma 3.4 and Theorem 3.6 argue
--   - encoding: instances where the optimal value u* > 0 → gᴰᵢ ≥ 0 for all i and gᴰ not all zero; reason: under gᴰ ≥ 0, u* ≥ ½Σᵢgᴰᵢ (Lemma 3.1), so u* > 0 iff gᴰ ≠ 0; gᴰ ≠ 0 is also Algorithm 1's input condition
--   - generalization: objective value at least (1 − ε)·u* → (1 − ε)·U(q') ≤ U(output) for every division q'; reason: for ε ≤ 1 this is equivalent (the optimum is attained); for ε > 1, (1 − ε)U(q') ≥ (1 − ε)u*, so the Lean bound implies the source's at q' optimal
--   - encoding: line 5 takes an optimal solution of C_P → for every selection sol with sol k optimal for C_{P_k} on every iteration k run; reason: the output depends on which optimum is taken; the claim holds for each choice
--   - encoding: E[uᴰ] of the returned division p → the interim utility at qOfP p = 2p − 1; reason: the same division in the auxiliary variables (Eqs. (1)–(2)); utilities are defined on q
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, Theorem 3.6, p.10 (FPTAS defined on p.10)

import Mathlib
import Definitions.Def_DivideChooseBayes_qOfP
import Definitions.Def_DivideChooseBayes_IsDivision
import Definitions.Def_DivideChooseBayes_normalPrior
import Definitions.Def_DivideChooseBayes_interimUtility
import Definitions.Def_DivideChooseBayes_IsCPOptimal
import Definitions.Def_DivideChooseBayes_algOutput

open MeasureTheory ProbabilityTheory

namespace DivideChooseBayes

/-- **Theorem 3.6 (Algorithm 1 is an FPTAS for nonnegative divider values).**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, Theorem 3.6, p.10: "When all gᴰᵢ ≥ 0, running Algorithm 1 with γ := (ε/2) · ∑ᵢ gᴰᵢ is a
fully polynomial-time approximation scheme with approximation parameter ε." FPTAS (p.10): "on
instances where the optimal value is u* > 0, for any ε > 0, it can find a solution with objective
value at least (1 − ε) · u* in time polynomial in both n and 1/ε."

Under independent normal priors `N(mᵢ, σᵢ²)` with `σᵢ > 0`, for divider values `gᴰᵢ ≥ 0` not all
zero and every `ε > 0`, run Algorithm 1 with `γ = (ε/2) ∑ᵢ gᴰᵢ`. Then:
1. the main loop runs exactly `⌈1/ε⌉` times;
2. on each iteration `k` the program `C_{P_k}` (n variables) has a nonempty, compact, convex
   feasible set and an affine objective, and attains its maximum;
3. for every selection `sol` of optimal solutions of these programs, the output `p` is a division
   and its interim expected utility is at least `(1 − ε) U(q')` for every division `q'`.

**Formalization Note.** "Polynomial time in n and 1/ε" is read as clauses 1–2: the number of
iterations depends on `ε` only, and each iteration is one convex program in `n` variables (the
algorithm has real inputs and exact conic optima, so no Turing-machine reading applies). With
`gᴰ ≥ 0` not all zero, `u* ≥ ½∑gᴰᵢ > 0`, so every instance has `u* > 0`. The guarantee is stated
against every division `q'`; for `ε ≤ 1` this is `≥ (1 − ε) u*`, and for `ε > 1` it is at least as
strong. The output `p` is evaluated through `q = 2p − 1` (Eq. (1)). -/
theorem theorem_3_6 {ι : Type*} [Fintype ι] (gD : ι → ℝ) (hgD₀ : ∀ i, 0 ≤ gD i)
    (hgD : ∃ i, gD i ≠ 0) (m σ : ι → ℝ) (hσ : ∀ i, 0 < σ i) (ε : ℝ) (hε : 0 < ε) :
    iterationCount gD (ε / 2 * ∑ i, gD i) = ⌈1 / ε⌉₊ ∧
      (∀ k < iterationCount gD (ε / 2 * ∑ i, gD i),
        (cpFeasibleSet gD m σ (algP gD (ε / 2 * ∑ i, gD i) k)).Nonempty ∧
          IsCompact (cpFeasibleSet gD m σ (algP gD (ε / 2 * ∑ i, gD i) k)) ∧
          Convex ℝ (cpFeasibleSet gD m σ (algP gD (ε / 2 * ∑ i, gD i) k)) ∧
          (∃ (c₀ : ℝ) (c : ι → ℝ), ∀ q,
            cpObjective gD (algP gD (ε / 2 * ∑ i, gD i) k) q = c₀ + ∑ i, c i * q i) ∧
          ∃ q, IsCPOptimal gD m σ (algP gD (ε / 2 * ∑ i, gD i) k) q) ∧
      ∀ sol : ℕ → ι → ℝ,
        (∀ k < iterationCount gD (ε / 2 * ∑ i, gD i),
          IsCPOptimal gD m σ (algP gD (ε / 2 * ∑ i, gD i) k) (sol k)) →
        (∀ i, algOutput gD (ε / 2 * ∑ i, gD i) sol i ∈ Set.Icc (0 : ℝ) 1) ∧
          ∀ q' : ι → ℝ, IsDivision q' →
            (1 - ε) * interimUtility (normalPrior m σ) gD q' ≤
              interimUtility (normalPrior m σ) gD (qOfP (algOutput gD (ε / 2 * ∑ i, gD i) sol)) := by sorry

end DivideChooseBayes
