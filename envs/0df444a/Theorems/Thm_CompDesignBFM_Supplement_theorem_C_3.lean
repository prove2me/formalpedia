-- Prove2me | Theorems.Thm_CompDesignBFM_Supplement_theorem_C_3
-- name    : CompDesignBFM.Supplement.theorem_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T21:09:10.205001+00:00
-- url     : https://prove2.me/theorems/c17a60ad-29e4-4cd3-a0a6-2a4ddc3675a4
-- title:
--   Theorem C.3 — in large markets $v(S^{(\beta)}(c))\ge\exp(-\beta/(1-\beta\lambda))\,\mathrm{OPT}$
-- statement:
--   Let $B>0$, $\beta>0$, $v$ normalized and $\beta$-self-bounding, and $c\ge0$ with $c_i/B\le\lambda$ for every $i$, where $\beta\lambda<1$. Then every global maximizer $S$ of $\Phi^{(\beta)}_c(S)=v(S)\prod_{i\in S}(1-\beta c_i/B)^+$, in particular $S^{(\beta)}(c)$, satisfies
--
--   $$v(S)\ge\exp\Bigl(-\frac{\beta}{1-\beta\lambda}\Bigr)\mathrm{OPT},\qquad \mathrm{OPT}=\max\Bigl\{v(T):\sum_{i\in T}c_i\le B\Bigr\}.\tag{38}$$
--
--   With Theorems C.1 and C.2 this gives a constant-factor truthful budget-feasible mechanism for $\beta$-self-bounding valuations in large markets.
--
--   Differences from the source:
--   - reading: β-self-bounding with β unrestricted → 0 < β; reason: Algorithm C.1 and Φ^{(β)} divide by β; the appendix treats β ≥ 1 classes and never β ≤ 0
--   - generalization: the global potential maximizer S^{(β)}(c) → every global maximizer S of Φ^{(β)}_c = pot v (B/β) c; reason: S^{(β)}(c) = Amc v (B/β) r c is a global maximizer, so the statement specializes to the source's
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Theorem C.3, eq. (38), p.48 (PDF 50)

import Mathlib
import Definitions.Def_CompDesignBFM_pot
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesignBFM_Supplement_IsBetaSelfBounding

namespace CompDesignBFM

namespace Supplement

/-- Theorem C.3 (large-market approximation), Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.48, PDF 50, eq. (38). Let `v` be a normalized
`β`-self-bounding valuation, and suppose `cᵢ/B ≤ λ` for every `i`, where `βλ < 1`. Then the global
potential maximizer satisfies `v(S^(β)(c)) ≥ exp(−β/(1 − βλ)) · OPT`.
**Formalization Note.** Stated for every global maximizer `S` of `Φ^(β)_c = pot v (B / β) c`
(`cᵢ/(B/β) = β cᵢ/B`), which includes `S^(β)(c) = Amc v (B / β) r c`. `OPT` is at the full budget `B`.
Costs are nonnegative. -/
theorem theorem_C_3 {n : ℕ} (v : Finset (Fin n) → ℝ) (B β : ℝ) (hB : 0 < B) (hβ : 0 < β)
    (hv0 : v ∅ = 0) (hv : IsBetaSelfBounding β v) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (l : ℝ) (hl : ∀ i, c i / B ≤ l) (hβl : β * l < 1)
    (S : Finset (Fin n)) (hS : ∀ T, pot v (B / β) c T ≤ pot v (B / β) c S) :
    Real.exp (-(β / (1 - β * l))) * OPT v B c ≤ v S := by sorry

end Supplement

end CompDesignBFM
