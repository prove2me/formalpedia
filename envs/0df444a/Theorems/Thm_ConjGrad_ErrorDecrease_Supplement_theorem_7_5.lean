-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_7_5
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_7_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T02:02:46.155118+00:00
-- url     : https://prove2.me/theorems/50ea0669-89b4-4d3e-9efc-b1353749921f
-- title:
--   Theorem 7:5 (corrected: $\bar y_{i-1}$ for the printed $y_{i-1}$) — $|h-x_i|<|h-\bar x_i|$ and $|h-\bar x_i|<|h-\bar x_{i-1}|$
-- statement:
--   With the cg-method for a real symmetric positive definite $A$, $Ah=k$, and the smoothed estimates $\bar x_i$ of (7:2), let $y_i=h-x_i$ and $\bar y_i=h-\bar x_i$. Then $y_i$ is shorter than $\bar y_i$,
--
--   $$|y_i|<|\bar y_i|\quad(0<i<m),$$
--
--   and $\bar y_i$ is shorter than $\bar y_{i-1}$ for $1\le i\le m$. (The paper prints "$\bar y_i$ is shorter than $y_{i-1}$" without the bar on $y_{i-1}$; that printed claim is false, and the paper's own proof, which moves along the segment from $\bar x_i$ to $\bar x_{i-1}$, establishes the barred comparison stated here.) At the endpoints $\bar y_0=y_0$ and $\bar y_m=y_m=0$.
--
--   Like the cg estimates (Theorem 6:3), the smoothed estimates approach $h$ monotonically in the Euclidean norm.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with the dot product $(x,y)=\sum_l x_ly_l$ and $|z|^2=(z,z)$. The cg-method is the published iteration `cgIter` of (5:1), 0-based, with no stopping test: once $r_m=0$ Lean's convention $t/0=0$ keeps $x_i=h$ and $r_i=p_i=0$ for $i\ge m$. $A$ is real, symmetric and positive definite (`A.PosDef`), the paper's standing assumption on p. 410. The integer $m$ is the step at which the cg-method terminates: $r_m=0$ and $r_j\neq0$ for $j<m$ (the paper's $x_m=h$; such an $m\le n$ exists by Theorem 4:2, so these hypotheses exclude no run).
--
--   Differences from the source:
--   - encoding: the paper's step index $i\ge1$ → Lean index $i+1$ with $i\ge0$; reason: avoids natural-number subtraction; same instances
--   - reading: the two comparisons stated without range → $0<i<m$ for $|y_i|<|\bar y_i|$, $1\le i\le m$ for $|\bar y_i|<|\bar y_{i-1}|$, plus the endpoint equalities; reason: at $i=0$ and $i=m$ the two error vectors coincide
--   - correction: the printed second sentence "$\bar y_i$ is shorter than $y_{i-1}$" → $|\bar y_i|<|\bar y_{i-1}|$; reason: typo (missing overbar). The printed claim is false: for $A=\mathrm{diag}(1,4,13)$, $k=(7,4,1)$, $x_0=0$ and $i=2$ one gets $|\bar y_2|^2=2401043347017/188540929369\approx12.735>|y_1|^2=310795/24843\approx12.510$; the paper's proof concludes that the distance from $h$ increases from $\bar x_i$ to $\bar x_{i-1}$, i.e. the barred statement
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 419, Theorem 7:5 (PDF p. 11)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 7:5 (Hestenes–Stiefel 1952, p. 419): `|yᵢ| < |ȳᵢ|` for `0 < i < m` and
`|ȳᵢ| < |ȳᵢ₋₁|` for `1 ≤ i ≤ m`, where `yᵢ = h − xᵢ`, `ȳᵢ = h − x̄ᵢ` and `m` is the step at which
the cg-method terminates; at `i = 0` and `i = m` the two error vectors coincide. Corrected: the
paper prints "`ȳᵢ` is shorter than `yᵢ₋₁`", which is false; its proof gives `|ȳᵢ| < |ȳᵢ₋₁|`. -/
theorem theorem_7_5 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (m : ℕ) (hm : (cgIter A k x₀ m).r = 0)
    (hact : ∀ j < m, (cgIter A k x₀ j).r ≠ 0) :
    (∀ i : ℕ, 0 < i → i < m →
      (h - (cgIter A k x₀ i).x) ⬝ᵥ (h - (cgIter A k x₀ i).x) <
        (h - smoothX A k x₀ i) ⬝ᵥ (h - smoothX A k x₀ i)) ∧
    (∀ i : ℕ, i + 1 ≤ m →
      (h - smoothX A k x₀ (i + 1)) ⬝ᵥ (h - smoothX A k x₀ (i + 1)) <
        (h - smoothX A k x₀ i) ⬝ᵥ (h - smoothX A k x₀ i)) ∧
    smoothX A k x₀ 0 = (cgIter A k x₀ 0).x ∧ smoothX A k x₀ m = (cgIter A k x₀ m).x := by sorry

end ConjGrad.ErrorDecrease.Supplement
