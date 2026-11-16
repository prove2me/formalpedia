-- Prove2me | Theorems.Thm_ElimAgree_Supplement_theorem_6_3
-- name    : ElimAgree.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:39:28.733447+00:00
-- url     : https://prove2.me/theorems/cdd7b4d7-cc58-438b-b3cb-414410495dbe
-- title:
--   Theorem 6.3 (The spectral bound transfers to elimination)
-- statement:
--   Let $k\ge1$, let $f_1,\dots,f_k$ be Boolean functions on finite domains and $\mu_i=\mu_{X_i}\times\mu_{Y_i}$ product distributions under which $h_i=(-1)^{f_i}$ is balanced, and put $\delta=\max_i\|H_i\|$. For every $0\le\epsilon<2^{-k}$,
--
--   $$R^{\mathrm{pub,com}}_\epsilon\big(\mathrm{Elim}(f_1,\dots,f_k)\big)\ \ge\ 2\log\frac1\delta+2\log(1-2^k\epsilon).$$
--
--   In particular, whenever $(-1)^f$ is balanced under the product distribution $\mu$,
--
--   $$R^{\mathrm{pub,com}}_\epsilon\big(\mathrm{Elim}(f^k)\big)\ \ge\ 2\log\frac1{\|H_\mu\|}+2\log(1-2^k\epsilon)\qquad\text{for every }k.$$
--
--   So for common output, elimination of any number of instances is as hard as computing one instance at constant advantage, as measured by the spectral bound.
--
--   **Formalization Note** Common output is the base convention (the parties may disagree on failed runs).
--
--   Differences from the source:
--   - reading: ϵ < 2^{−k} (an error probability) → 0 ≤ ϵ < 2^{−k}; reason: for ϵ < 0 the constraint, read in [0,∞], would mean zero error while the bound grows; the source only means probabilities
--   - reading: δ = max_i ∥H_i∥ (k ≥ 1 implicit) → 1 ≤ k in the first clause; reason: the maximum is over a nonempty index set
--   - encoding: a lower bound on R_ϵ (least worst-case cost) → every protocol of cost c (all trees in its support of depth ≤ c) with pointwise error ≤ ϵ has c ≥ the bound; reason: R is the least such cost, so the two say the same; avoids sInf of a possibly empty set
--   - encoding: product distributions µ_i → pairs of laws on finite types; reason: same objects
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Theorem 6.3, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_ElimAgree_IsLaw
import Definitions.Def_ElimAgree_Supplement_Models
import Definitions.Def_ElimAgree_Supplement_SignOp

namespace ElimAgree

namespace Supplement

/-- Theorem 6.3 (The spectral bound transfers to elimination), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.24. Let `f_1, …, f_k` be Boolean
functions and `µ_i` product distributions under which `h_i = (−1)^{f_i}` is balanced, and put
`δ = max_i ∥H_i∥`. For every `ϵ < 2^{−k}`,
`R^{pub,com}_ϵ(Elim(f_1, …, f_k)) ≥ 2 log(1/δ) + 2 log(1 − 2^kϵ)`. In particular
`R^{pub,com}_ϵ(Elim(f^k)) ≥ 2 log(1/∥H_µ∥) + 2 log(1 − 2^kϵ)` for every `k`, whenever `(−1)^f` is
balanced under the product distribution `µ`.

**Formalization Note.** A product distribution `µ_i = µ_{X_i} × µ_{Y_i}` is a pair of laws on finite
types. The lower bound on `R^{pub,com}_ϵ` is stated for every common-output protocol (base `comErr`,
which allows disagreement) of cost `c` with pointwise error at most `ϵ`. `ϵ ≥ 0` (an error
probability) and `k ≥ 1` (so that the maximum is over a nonempty set) are the paper's ranges. -/
theorem theorem_6_3 :
    (∀ (k : ℕ) (hk : 1 ≤ k) (X Y : Fin k → Type) [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
      (f : ∀ i, X i → Y i → Bool) (μX : ∀ i, X i → ℝ) (μY : ∀ i, Y i → ℝ),
      (∀ i, IsLaw (μX i)) → (∀ i, IsLaw (μY i)) → (∀ i, Balanced (μX i) (μY i) (f i)) →
      ∀ ε : ℝ, 0 ≤ ε → ε < 1 / 2 ^ k →
      ∀ (c : ℕ) (μ : PMF (ComProtG (∀ i, X i) (∀ i, Y i) (Fin k → Bool))), CostLE μ c →
      (∀ x y, comErr (elimAns f) μ x y ≤ ENNReal.ofReal ε) →
      2 * Real.logb 2 (1 / Finset.univ.sup' ⟨⟨0, hk⟩, Finset.mem_univ _⟩
          (fun i => signNorm (μX i) (μY i) (f i))) +
        2 * Real.logb 2 (1 - 2 ^ k * ε) ≤ (c : ℝ)) ∧
    (∀ (X Y : Type) [Fintype X] [Fintype Y] (f : X → Y → Bool) (μX : X → ℝ) (μY : Y → ℝ),
      IsLaw μX → IsLaw μY → Balanced μX μY f →
      ∀ (k : ℕ) (ε : ℝ), 0 ≤ ε → ε < 1 / 2 ^ k →
      ∀ (c : ℕ) (μ : PMF (ComProtG (Fin k → X) (Fin k → Y) (Fin k → Bool))), CostLE μ c →
      (∀ x y, comErr (elimAns (X := fun _ => X) (Y := fun _ => Y) (fun _ : Fin k => f)) μ x y ≤
        ENNReal.ofReal ε) →
      2 * Real.logb 2 (1 / signNorm μX μY f) + 2 * Real.logb 2 (1 - 2 ^ k * ε) ≤ (c : ℝ)) := by sorry

end Supplement

end ElimAgree
