-- Prove2me | Theorems.Thm_CNFLearnMQ_Supplement_theorem_6_3
-- name    : CNFLearnMQ.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:06:05.600615+00:00
-- url     : https://prove2.me/theorems/e2b7bf4f-058f-4a6f-a94b-49b44abee933
-- title:
--   Theorem 6.3 — each target clause is induced by a core with probability at least $1/(4^k n^{\eta_k})$
-- statement:
--   Let $k\ge10^5$ and $\alpha>0$ with $\alpha\le 2^{k-30k^{4/5}\log k}/(2^{10}e^2k^8)$, and $\eta_k=4096k^{6/5}2^{-k^{4/5}}$. There is $n_0=n_0(k,\alpha)$ such that the following holds for every $n\ge n_0$. Let $\Phi=(V,\mathcal C)$ be a formula that the random model $\Phi(k,n,\lfloor\alpha n\rfloor)$ can produce, which is satisfiable and has Properties (i)–(vi) of Lemma 6.2. For every target clause $c^\star\in\mathcal C$, writing $C^\star=\mathrm{vbl}(c^\star)$,
--   $$\Pr_{X\sim\mu_\Phi}\bigl[C^\star\in\mathcal R_X\ \text{and}\ c(X,C^\star)=c^\star\bigr]\ \ge\ \frac{1}{4^k\cdot n^{\eta_k}} .$$
--
--   Here $\mathcal R_X$ is the family of cores of the solution $X$ and $c(X,R)=(R,\neg X_R)$ the subclause induced by a core. The bound says that a uniform solution reveals each clause of the formula, as one of its cores, with probability $n^{-o_k(1)}$; it is what makes $N\approx 4^kn^{\eta_k}\ln(n/\delta)$ samples enough for CoreSieve in Theorem 6.1.
--
--   Differences from the source:
--   - reading: Theorem 6.3 for the formula fixed in §6.2 → hypotheses $k\ge10^5$, $0<\alpha\le\alpha_{\max}(k)$, $n\ge n_0(k,\alpha)$, $\Phi$ in the support of $\Phi(k,n,\lfloor\alpha n\rfloor)$, satisfiable, with Properties (i)–(vi) of Lemma 6.2; reason: these are the standing assumptions of §6 (pp.37–38: "any fixed $\Phi$ satisfying these properties, which we assume throughout the rest of this section")
--   - encoding: $C^\star\in\mathcal R_X$ and $c(X,C^\star)=c^\star$ → `support cstar ∈ cores Φ X ∧ inducedClause X (support cstar) = cstar` under the published uniform law on solutions; reason: the published clause type stores the satisfying literal value, so this says $X_{C^\star}=\neg\sigma_{c^\star}$
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Theorem 6.3, p.39; standing assumptions of §6, pp.37–38

import Mathlib
import Definitions.Def_CNFLearnMQ_Supplement_Lemma62Props
import Definitions.Def_CNFLearnMQ_memOracle
import Definitions.Def_CNFLearnMQ_OProg

set_option autoImplicit false

namespace CNFLearnMQ.Supplement

open CNFLearning873.Valiant CNFLearnMQ

/-- Theorem 6.3, p.39 (Feng, Yu, Zhang, *Learning CNF Formulas with Uniform Random Solutions and
Membership Queries*, STOC 2027 submission (manuscript sha256 519ee6d4…)), with the standing
assumptions of §6 (pp.37–38). Let `k ≥ 10⁵` and `α > 0` with
`α ≤ 2^{k − 30k^{4/5} log k}/(2^{10}e²k⁸)`. There is `n₀ = n₀(k, α)` such that for every `n ≥ n₀`,
every formula `Φ = (V, C)` that the random model `Φ(k, n, ⌊αn⌋)` can produce, is satisfiable and
has Properties (i)–(vi) of Lemma 6.2, and every target clause `c⋆ ∈ C`, writing `C⋆ = vbl(c⋆)`,
`P_{X∼µ_Φ}[C⋆ ∈ R_X and c(X, C⋆) = c⋆] ≥ 1/(4^k · n^{η_k})`.

**Formalization Note** The paper states Theorem 6.3 for "any fixed `Φ` satisfying these properties,
which we assume throughout the rest of this section" (p.38), with `k, α` as in Theorem 6.1 and `n`
sufficiently large (p.37); these are the hypotheses here. The published clause type stores the
satisfying literal value, so `c(X, C⋆) = c⋆` (`inducedClause X C⋆ = c⋆`) says `X_{C⋆} = ¬σ_{c⋆}`.
`η_k` is the real exponent `etaK k`. -/
theorem theorem_6_3 (k : ℕ) (α : ℝ) (hk : 10 ^ 5 ≤ k) (hα : 0 < α)
    (hαk : α ≤ densityBound k) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ Φ ∈ (randomCNF k n ⌊α * n⌋₊).support,
      ∀ h : (solutions Φ).Nonempty, Lemma62Props k α n Φ → ∀ cstar ∈ Φ,
        ENNReal.ofReal (1 / ((4 : ℝ) ^ k * (n : ℝ) ^ etaK k)) ≤
          prob (solutionPMF Φ h)
            (fun X => support cstar ∈ cores Φ X ∧ inducedClause X (support cstar) = cstar) := by sorry

end CNFLearnMQ.Supplement
