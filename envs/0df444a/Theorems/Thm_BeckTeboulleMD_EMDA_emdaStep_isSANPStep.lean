-- Prove2me | Theorems.Thm_BeckTeboulleMD_EMDA_emdaStep_isSANPStep
-- name    : BeckTeboulleMD.EMDA.emdaStep_isSANPStep
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:01:37.011444+00:00
-- url     : https://prove2.me/theorems/b3f96e0d-ae49-443d-960e-e9617b81a253
-- title:
--   The EDA update is the SANP step (3.11) for the entropy on Δ
-- statement:
--   Let $\Delta\subset\mathbb R^n$ be the unit simplex, $x\in\Delta$ with all coordinates positive, $g\in\mathbb R^n$ and $t>0$, and let $p$ be the EMDA update
--   $$
--   p_j=\frac{x_j e^{-t g_j}}{\sum_{i=1}^n x_i e^{-t g_i}} .
--   $$
--   Then:
--
--   1. $p\in\Delta$ and all coordinates of $p$ are positive;
--   2. $p$ minimizes $y\mapsto\langle y,g\rangle+t^{-1}B_{\psi_e}(y,x)$ over $\Delta$;
--   3. $p$ is the unique minimizer.
--
--   So $p=\operatorname{argmin}_{y\in\Delta}\{\langle y,g\rangle+t^{-1}B_{\psi_e}(y,x)\}$: the explicit entropic descent update is the SANP step (3.11) with $\psi=\psi_e$ and $X=\Delta$, and it keeps the iterates in the relative interior of $\Delta$.
--
--   This identification is what lets the general efficiency estimates of §4 apply to the entropic mirror descent algorithm.
--
--   **Formalization Note** $\langle y,g\rangle=\sum_j y_jg_j$ and $B_{\psi_e}$ uses the real formula of the entropy.
--
--   Differences from the source:
--   - reading: x¹ ∈ int Δ (Δ has empty interior in ℝⁿ) → x ∈ stdSimplex with all coordinates positive; reason: the paper means the relative interior; with empty interior the claim would be vacuous
--   - generalization: the EDA iteration with t_k = √(2 ln n)/L_f · 1/√k and g = f′(x^k) ∈ ∂f(x^k) → every step t > 0 and every vector g; reason: the paper's t_k (when positive) and f′(x^k) are instances, so the statement specializes to the paper's
--   - encoding: x^{k+1} = argmin_{x∈Δ} {⟨x, f′(x^k)⟩ + t_k⁻¹ B_ψe(x, x^k)} → the update is a minimizer and the unique one (clauses 2 and 3), with ⟨y, g⟩ = ∑ j, y j * g j; reason: 'is the argmin' is exactly 'minimizes, uniquely'
-- source:
--   Beck & Teboulle, Mirror descent and nonlinear projected subgradient methods for convex optimization, Oper. Res. Lett. 31 (2003) 167–175, doi:10.1016/s0167-6377(02)00231-6, §5, the sentence introducing the EDA and the EDA box, printed p. 174 (PDF p. 8); SANP (3.11), printed p. 170 (PDF p. 4)

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_bregman
import Definitions.Def_BeckTeboulleMD_EMDA_entropy
import Definitions.Def_BeckTeboulleMD_EMDA_emdaStep

namespace BeckTeboulleMD.EMDA

/-- **The EDA update is the SANP step for the entropy on the simplex.**
Beck & Teboulle, *Mirror descent and nonlinear projected subgradient methods for convex
optimization*, Oper. Res. Lett. 31 (2003), §5, the sentence introducing the
EDA, printed p. 174 (PDF p. 8): "Using the entropy function ψ_e in (3.12), we thus obtain a very
simple algorithm for minimizing the convex function f over Δ, which is given explicitly by
The entropic descent algorithm (EDA) Start with x¹ ∈ int Δ and generate for k = 1, …, the
sequence {x^k} via: x_j^{k+1} = x_j^k e^{−t_k f′_j(x^k)} / Σ_{j=1}^n x_j^k e^{−t_k f′_j(x^k)}."
Here SANP is (3.11), printed p. 170 (PDF p. 4):
"x^{k+1} = argmin_{x∈X} { ⟨x, f′(x^k)⟩ + (1/t_k) B_ψ(x, x^k) }, t_k > 0".

For `x` in the relative interior of `Δ`, any vector `g` and any `t > 0`, the point
`p = emdaStep t x g`:
1. lies in `Δ` and has positive coordinates;
2. minimizes `y ↦ ⟨y, g⟩ + t⁻¹ B_{ψ_e}(y, x)` over `Δ`;
3. is the unique minimizer.

**Formalization Note.** `Δ` is `stdSimplex ℝ (Fin n)`, `int Δ` is read as the relative interior
(positive coordinates), `⟨y, g⟩` is `∑ j, y j * g j` and `B_{ψ_e}` is `bregman entropy`. Clauses
2–3 are `IsSANPStep` for `X = Δ`, `ψ = entropy` and the functional `y ↦ ∑ j, y j * g j`, written
out with explicit sums, plus uniqueness. -/
theorem emdaStep_isSANPStep {n : ℕ} (x : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n))
    (hxpos : ∀ j, 0 < x j) (g : Fin n → ℝ) (t : ℝ) (ht : 0 < t) :
    (emdaStep t x g ∈ stdSimplex ℝ (Fin n) ∧ ∀ j, 0 < emdaStep t x g j) ∧
    (∀ y ∈ stdSimplex ℝ (Fin n),
      ∑ j, emdaStep t x g j * g j + t⁻¹ * bregman entropy (emdaStep t x g) x ≤
        ∑ j, y j * g j + t⁻¹ * bregman entropy y x) ∧
    (∀ q ∈ stdSimplex ℝ (Fin n),
      (∀ y ∈ stdSimplex ℝ (Fin n),
        ∑ j, q j * g j + t⁻¹ * bregman entropy q x ≤ ∑ j, y j * g j + t⁻¹ * bregman entropy y x) →
      q = emdaStep t x g) := by sorry

end BeckTeboulleMD.EMDA
