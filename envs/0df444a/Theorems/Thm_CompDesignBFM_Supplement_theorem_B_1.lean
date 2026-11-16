-- Prove2me | Theorems.Thm_CompDesignBFM_Supplement_theorem_B_1
-- name    : CompDesignBFM.Supplement.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:07:22.131125+00:00
-- url     : https://prove2.me/theorems/50698e8b-6a01-4aba-838a-aaf4cfe31655
-- title:
--   Theorem B.1 — every randomized compensation rule has PoA $\Omega(n^{1/5})$ on the XOS instance (34)
-- statement:
--   Consider the instance of App. B: an integer $k\ge4$, $m=k^4$ groups $N_1,\dots,N_m$ of $k$ agents each ($n=k^5$), budget $B=1$, and the XOS value
--   $$v(S)=\max\Bigl\{\tfrac2m|S|,\ \max_j|S\cap N_j|\Bigr\}.$$
--   There is an absolute constant $C_0>0$ such that for every $k\ge4$ and every randomized compensation rule $P$, a distribution over deterministic rules $p$ that are nonnegative, pay nothing outside the participating set, are budget feasible and have a pure Nash equilibrium at every nonnegative cost vector, there is a cost vector $c\ge0$ with
--   $$C_0\,k\cdot\mathbb E_{p\sim P}\Bigl[\min_{S\in E(p,c)}v(S)\Bigr]\le\mathrm{OPT}(c).$$
--   Since $n^{1/5}=k$, the pure price of anarchy of every such rule is $\Omega(n^{1/5})$, even with unlimited computation and value queries. So the constant price of anarchy of the monotone submodular case does not extend to XOS valuations.
--
--   **Formalization Note** A randomized rule is a probability space with a measurable map to payment rules; the integrability of the worst-equilibrium value is part of the conclusion.
--
--   Differences from the source:
--   - encoding: PoA at least Ω(n^{1/5}) → ∃ C₀ > 0, chosen before k, with C₀·k·E[worst equilibrium value] ≤ OPT at some cost vector c ≥ 0; reason: n^{1/5} = k exactly on the instance; the multiplied form is PoA ≥ C₀k including the paper's infinite ratio when the denominator is zero
--   - encoding: a randomized compensation rule, a distribution over deterministic rules → a probability space (Ω : Type, P) with a measurable realization map p; reason: any distribution over payment rules is the law of such a map
--   - reading: guarantees existence of pure Nash equilibria → every realization has a pure equilibrium at every nonnegative cost vector; reason: V_p(c) of the proof is defined for every rule in the support at every cost vector
--   - encoding: E_{p∼P}[V_p(c)] → Bochner integral, with integrability as a conclusion conjunct; reason: excludes the junk value 0 of a non-integrable integrand
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Theorem B.1, p.43 (PDF 45), instance (34) and B = 1, m = k⁴, n = k⁵, k ≥ 4, p.41 (PDF 43)

import Mathlib
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesignBFM_Supplement_IsPNEOf
import Definitions.Def_CompDesignBFM_Supplement_IsCompRule
import Definitions.Def_CompDesignBFM_Supplement_worstEqValue
import Definitions.Def_CompDesignBFM_Supplement_lbValue

namespace CompDesignBFM

namespace Supplement

/-- Theorem B.1 (PoA lower bound for XOS), Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.43, PDF 45. On the instance of App. B (the XOS value
(34) with `m = k⁴` groups of `k` agents, `n = k⁵`, `B = 1`, `k ≥ 4`), every randomized, nonnegative,
cost-oblivious, budget-feasible compensation rule that guarantees existence of pure Nash equilibria has
pure price of anarchy at least `Ω(n^(1/5))`.
**Formalization Note.** `Ω(n^(1/5))` is a constant `C₀ > 0`, chosen before `k`, with
`PoA ≥ C₀ k` (`n^(1/5) = k`). A randomized rule is a probability space `(Ω, P)` (`Ω : Type`) with a
measurable realization map `p`; each realization is a compensation rule with budget `1` and has a pure
equilibrium at every nonnegative cost vector. Cost obliviousness and unlimited computation are by type:
`p ω` is an arbitrary function of the participating set. "PoA ≥ C₀ k" at some cost vector `c` is
`C₀ k · E_ω[worst equilibrium value] ≤ OPT`, which also covers the paper's "infinite when the
denominator is zero"; integrability of the worst-equilibrium value is part of the conclusion. -/
theorem theorem_B_1 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ k : ℕ, 4 ≤ k →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure P]
        (p : Ω → Finset (Fin (k ^ 5)) → Fin (k ^ 5) → ℝ), Measurable p →
        (∀ ω, IsCompRule 1 (p ω)) →
        (∀ ω (c : Fin (k ^ 5) → ℝ), (∀ i, 0 ≤ c i) → ∃ S, IsPNEOf (p ω) c S) →
        ∃ c : Fin (k ^ 5) → ℝ, (∀ i, 0 ≤ c i) ∧
          MeasureTheory.Integrable (fun ω => worstEqValue (p ω) (lbValue k) c) P ∧
          C₀ * k * ∫ ω, worstEqValue (p ω) (lbValue k) c ∂P ≤ OPT (lbValue k) 1 c := by sorry

end Supplement

end CompDesignBFM
