-- Prove2me | Theorems.Thm_ElimAgree_Supplement_theorem_7_2
-- name    : ElimAgree.Supplement.theorem_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:40:28.72486+00:00
-- url     : https://prove2.me/theorems/2472cd25-9605-4b36-97e8-2d96d6b6f350
-- title:
--   Theorem 7.2 (Spectral bounds without balance)
-- statement:
--   Let $f$ be a Boolean function on finite $\mathcal X\times\mathcal Y$, $\mu=\mu_X\times\mu_Y$ any product distribution, and $s=\|H_\mu\|$. For every $k\ge1$ and $0<g\le1$,
--
--   $$R^{\mathrm{pub,com}}_{(1-g)2^{-k}}\big(\mathrm{Elim}(f^k)\big)\ge\Big[2\log\frac1s+2\log g\Big]_+-10,$$
--
--   $$R^{\mathrm{pub},A}_{(1-g)2^{-k}}\big(\mathrm{Elim}(f^k)\big)\ge\Big[2\log\frac1s-\log k+2\log g\Big]_+-10,$$
--
--   where the local-output bound allows the output party to be designated at each leaf. The same bounds with $g=1$ hold for the worst-case expected communication of zero-error protocols in either convention: every zero-error common-output protocol has worst-case expected communication at least $[2\log(1/s)]_+-10$, and every zero-error protocol with the output party designated at each leaf at least $[2\log(1/s)-\log k]_+-10$.
--
--   So no balance assumption on $f$ is needed: any spectral bound under a product distribution transfers to elimination of any number of instances, up to an additive constant.
--
--   **Formalization Note** Lower bounds on $R$ are stated for every protocol of cost $c$ with that pointwise error. The zero-error bounds compare in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: a lower bound on R_ϵ (least worst-case cost) → every protocol of cost c (all trees in its support of depth ≤ c) with pointwise error ≤ ϵ has c ≥ the bound; reason: R is the least such cost, so the two say the same; avoids sInf of a possibly empty set
--   - reading: zero-error bounds "in either convention" (local output allowing a designated party) → common output, and output party designated at each leaf; reason: the stronger of the two readings of the local convention; it contains the Alice-output protocols
--   - encoding: worst-case expected communication ≥ b → ENNReal.ofReal b ≤ sup over inputs of the expected path length; reason: a bound b ≤ 0 is satisfied either way
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Theorem 7.2, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_ElimAgree_IsLaw
import Definitions.Def_ElimAgree_Supplement_Models
import Definitions.Def_ElimAgree_Supplement_SignOp

namespace ElimAgree

namespace Supplement

/-- Theorem 7.2 (Spectral bounds without balance), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.27. Let `f` be a Boolean function,
`µ = µ_X × µ_Y` any product distribution, and `s = ∥H_µ∥` the norm of the normalized operator with
kernel `h = (−1)^f`. For every `k ≥ 1` and `0 < g ≤ 1`,
`R^{pub,com}_{(1−g)2^{−k}}(Elim(f^k)) ≥ [2 log(1/s) + 2 log g]_+ − 10` and
`R^{pub,A}_{(1−g)2^{−k}}(Elim(f^k)) ≥ [2 log(1/s) − log k + 2 log g]_+ − 10`, where the local-output
bound allows the output party to be designated at each leaf. The same bounds with `g = 1` hold for
the worst-case expected communication of zero-error protocols in either convention.

**Formalization Note.** Lower bounds are stated for every protocol of cost `c` with pointwise error
at most `(1 − g)2^{−k}`: common output (base `comErr`, disagreement allowed) and designated output
party (base `desErr`). Zero error is failure probability `0` on every input; the worst-case expected
communication is `worstExpComm` (in `ℝ≥0∞`, with the bound passed through `ENNReal.ofReal`). In the
local convention the zero-error clause is stated with the output party designated at each leaf,
which contains the Alice-output protocols. -/
theorem theorem_7_2 {X Y : Type} [Fintype X] [Fintype Y] (f : X → Y → Bool) (μX : X → ℝ)
    (μY : Y → ℝ) (hμX : IsLaw μX) (hμY : IsLaw μY) (k : ℕ) (hk : 1 ≤ k) :
    (∀ g : ℝ, 0 < g → g ≤ 1 →
      ∀ (c : ℕ) (μ : PMF (ComProtG (Fin k → X) (Fin k → Y) (Fin k → Bool))), CostLE μ c →
      (∀ x y, comErr (elimAns (X := fun _ => X) (Y := fun _ => Y) (fun _ : Fin k => f)) μ x y ≤
        ENNReal.ofReal ((1 - g) / 2 ^ k)) →
      max (2 * Real.logb 2 (1 / signNorm μX μY f) + 2 * Real.logb 2 g) 0 - 10 ≤ (c : ℝ)) ∧
    (∀ g : ℝ, 0 < g → g ≤ 1 →
      ∀ (c : ℕ) (μ : PMF (DesProt (Fin k → X) (Fin k → Y) (Fin k → Bool))), CostLE μ c →
      (∀ x y, desErr (elimAns (X := fun _ => X) (Y := fun _ => Y) (fun _ : Fin k => f)) μ x y ≤
        ENNReal.ofReal ((1 - g) / 2 ^ k)) →
      max (2 * Real.logb 2 (1 / signNorm μX μY f) - Real.logb 2 k + 2 * Real.logb 2 g) 0 - 10 ≤
        (c : ℝ)) ∧
    (∀ μ : PMF (ComProtG (Fin k → X) (Fin k → Y) (Fin k → Bool)),
      (∀ x y, comErr (elimAns (X := fun _ => X) (Y := fun _ => Y) (fun _ : Fin k => f)) μ x y = 0) →
      ENNReal.ofReal (max (2 * Real.logb 2 (1 / signNorm μX μY f)) 0 - 10) ≤ worstExpComm μ) ∧
    (∀ μ : PMF (DesProt (Fin k → X) (Fin k → Y) (Fin k → Bool)),
      (∀ x y, desErr (elimAns (X := fun _ => X) (Y := fun _ => Y) (fun _ : Fin k => f)) μ x y = 0) →
      ENNReal.ofReal (max (2 * Real.logb 2 (1 / signNorm μX μY f) - Real.logb 2 k) 0 - 10) ≤
        worstExpComm μ) := by sorry

end Supplement

end ElimAgree
