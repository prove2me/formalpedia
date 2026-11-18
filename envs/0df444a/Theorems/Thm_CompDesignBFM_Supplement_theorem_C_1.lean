-- Prove2me | Theorems.Thm_CompDesignBFM_Supplement_theorem_C_1
-- name    : CompDesignBFM.Supplement.theorem_C_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-15T21:07:56.183463+00:00
-- url     : https://prove2.me/theorems/74f5090d-8961-493b-9b82-bb362ff5ae9a
-- title:
--   Theorem C.1 — $S^{(\beta)}(c)$ is a pure equilibrium of the scaled marginal-contribution rule
-- statement:
--   Let $B>0$, $\beta>0$ and $v$ normalized and $\beta$-self-bounding. Let $S^{(\beta)}(c)$ be the global maximizer of
--   $$\Phi^{(\beta)}_c(S)=v(S)\prod_{i\in S}\Bigl(1-\frac{\beta c_i}{B}\Bigr)^+,$$
--   ties broken by a fixed total order on $2^N$ in which $\emptyset$ comes first. For every cost vector $c\ge0$, $S^{(\beta)}(c)$ is a pure Nash equilibrium of the game induced by the scaled marginal-contribution rule $p_i(S)=\frac B\beta\,\frac{v(S)-v(S\setminus\{i\})}{v(S)}$ (Algorithm C.1).
--
--   This is the equilibrium-existence step of the extension of the framework from self-bounding to $\beta$-self-bounding valuations.
--
--   Differences from the source:
--   - reading: β-self-bounding with β unrestricted → 0 < β; reason: Algorithm C.1 and Φ^{(β)} divide by β; the appendix treats β ≥ 1 classes and never β ≤ 0
--   - encoding: S^{(β)}(c), the maximizer of Φ^{(β)}_c with ties broken by a fixed total order with ∅ first → Amc v (B/β) r c with IsPriority r; reason: pot v (B/β) c = Φ^{(β)}_c because c_i/(B/β) = βc_i/B
--   - encoding: every cost vector c → every nonnegative cost vector; reason: the section defines Φ^{(β)}_c for any nonnegative vector c (p.45)
-- source:
--   Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, Theorem C.1, p.45 (PDF 47)

import Mathlib
import Definitions.Def_CompDesignBFM_IsPriority
import Definitions.Def_CompDesignBFM_Amc
import Definitions.Def_CompDesignBFM_Supplement_IsBetaSelfBounding
import Definitions.Def_CompDesignBFM_Supplement_IsPNEOf
import Definitions.Def_CompDesignBFM_Supplement_scaledPay

namespace CompDesignBFM

namespace Supplement

/-- Theorem C.1 (pure equilibrium), Anagnostides et al., From Compensation Design to Budget-Feasible Mechanisms, arXiv:2608.04337, p.45, PDF 47. Let `v` be normalized and `β`-self-bounding.
For every cost vector `c`, `S^(β)(c)` is a pure Nash equilibrium of the game induced by the scaled
marginal-contribution rule of Algorithm C.1.
**Formalization Note.** `S^(β)(c)`, the global maximizer of `Φ^(β)_c(S) = v(S) ∏_(i ∈ S) (1 − β cᵢ/B)₊`
with ties broken by a fixed total order with `∅` first, is `Amc v (B / β) r c` for a priority `r`
(`IsPriority r`): `cᵢ/(B/β) = β cᵢ/B`. Cost vectors are nonnegative ("for any nonnegative vector c",
p.45). `B > 0` and `β > 0` are the model's. -/
theorem theorem_C_1 {n : ℕ} (v : Finset (Fin n) → ℝ) (B β : ℝ) (hB : 0 < B) (hβ : 0 < β)
    (hv0 : v ∅ = 0) (hv : IsBetaSelfBounding β v) (r : Finset (Fin n) → ℕ) (hr : IsPriority r)
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) :
    IsPNEOf (scaledPay v B β) c (Amc v (B / β) r c) := by sorry

end Supplement

end CompDesignBFM
