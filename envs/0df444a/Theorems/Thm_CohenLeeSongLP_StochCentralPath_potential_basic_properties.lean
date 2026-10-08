-- Prove2me | Theorems.Thm_CohenLeeSongLP_StochCentralPath_potential_basic_properties
-- name    : CohenLeeSongLP.StochCentralPath.potential_basic_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:08:04.810082+00:00
-- url     : https://prove2.me/theorems/68223400-ebc0-490e-bf74-2b692cbd9395
-- title:
--   Lemma 4.12 — basic properties of the potential $\Phi_\lambda$
-- statement:
--   In the paper's setting $n\ge10$, let $\Phi_\lambda(r)=\sum_{i=1}^n\cosh(\lambda r_i)$ for some $\lambda>0$, with gradient $\nabla\Phi_\lambda(r)=(\lambda\sinh(\lambda r_i))_i$ and local norm $\|v\|^2_{\nabla^2\Phi_\lambda(r)}=\sum_i\lambda^2\cosh(\lambda r_i)v_i^2$. For any vector $r\in\mathbb R^n$:
--
--   1. for any vector $v$ with $\|v\|_\infty\le 1/\lambda$,
--   $$\Phi_\lambda(r+v)\le\Phi_\lambda(r)+\langle\nabla\Phi_\lambda(r),v\rangle+2\|v\|^2_{\nabla^2\Phi_\lambda(r)};$$
--   2. $\|\nabla\Phi_\lambda(r)\|_2\ge\frac{\lambda}{\sqrt n}(\Phi_\lambda(r)-n)$;
--   3. $\big(\sum_{i=1}^n\lambda^2\cosh^2(\lambda r_i)\big)^{1/2}\le\lambda\sqrt n+\|\nabla\Phi_\lambda(r)\|_2$.
--
--   These three inequalities are the deterministic ingredients of the expected-decrease estimate for the potential (Lemma 4.13).
--
--   **Formalization Note** $\|v\|_\infty\le1/\lambda$ is stated as $|v_i|\le 1/\lambda$ for every $i$. The bound $1/\lambda$ is the one printed in the statement (the proof writes $1/(2\lambda)$, but the argument works for $1/\lambda$).
-- source:
--   Cohen, Lee and Song, Solving Linear Programs in the Current Matrix Multiplication Time, J. ACM 68(1), Article 3 (2021), p. 3:17, Lemma 4.12

import Mathlib
import Definitions.Def_CohenLeeSongLP_StochCentralPath_Basic

namespace CohenLeeSongLP.StochCentralPath

/-- Lemma 4.12 (p. 3:17): basic properties of `Φ_λ(r) = ∑ᵢ cosh(λ rᵢ)` for the section's
`n ≥ 10`, `λ > 0` and any
`r ∈ ℝⁿ`:
1. if `‖v‖_∞ ≤ 1/λ`, then `Φ_λ(r+v) ≤ Φ_λ(r) + ⟨∇Φ_λ(r), v⟩ + 2‖v‖²_{∇²Φ_λ(r)}`;
2. `‖∇Φ_λ(r)‖₂ ≥ (λ/√n)(Φ_λ(r) − n)`;
3. `(∑ᵢ λ² cosh²(λ rᵢ))^{1/2} ≤ λ√n + ‖∇Φ_λ(r)‖₂`. -/
theorem potential_basic_properties {n : ℕ} (hn : 10 ≤ n) (lam : ℝ) (hlam : 0 < lam)
    (r : Fin n → ℝ) :
    (∀ v : Fin n → ℝ, (∀ i, |v i| ≤ 1 / lam) →
      potential lam (fun i => r i + v i) ≤
        potential lam r + ∑ i, potentialGrad lam r i * v i + 2 * hessNormSq lam r v) ∧
    lam / Real.sqrt n * (potential lam r - n) ≤ norm2 (potentialGrad lam r) ∧
    Real.sqrt (∑ i, lam ^ 2 * Real.cosh (lam * r i) ^ 2) ≤
      lam * Real.sqrt n + norm2 (potentialGrad lam r) := by sorry

end CohenLeeSongLP.StochCentralPath
