-- Prove2me | Theorems.Thm_DNNProj_proposition_7
-- name    : DNNProj.proposition_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:16:20.564046+00:00
-- url     : https://prove2.me/theorems/9534f09a-961e-4bd4-84f6-0ccebd160330
-- title:
--   Proposition 7 — $\mathcal N_{\mathbb S^n_+}(\bar S)$ is polyhedral iff $|\gamma|\ge n-1$; $0\in\bar X+\operatorname{ri}\mathcal N_{\mathbb S^n_+}(\bar S)$ iff $|\beta|=0$
-- statement:
--   Let $\bar S\in\mathbb S^n_+$ and $0\in\bar X+\partial\delta_{\mathbb S^n_+}(\bar S)$, and let $\alpha,\beta,\gamma$ be the index sets (15) of the positive, zero and negative eigenvalues of $\bar Z=\bar X-\bar S$. Then:
--
--   1. $\mathcal N_{\mathbb S^n_+}(\bar S)$ is a polyhedral set if and only if $|\gamma|\ge n-1$;
--   2. $0\in\bar X+\operatorname{ri}\big(\mathcal N_{\mathbb S^n_+}(\bar S)\big)$ if and only if $|\beta|=0$, i.e.,
--   $$\operatorname{rank}(\bar X)+\operatorname{rank}(\bar S)=n.$$
--
--   Part (b) is the strict complementarity condition behind Corollary 1(ii), part (a) behind Corollary 1(i).
--
--   **Formalization Note** $0\in\bar X+\partial\delta(\bar S)$ is $-\bar X\in\partial\delta_{\mathbb S^n_+}(\bar S)$. Polyhedrality and the relative interior are taken in $\mathbb S^n$. $|\gamma|\ge n-1$ is compared in $\mathbb Z$. Part (b) states both printed equivalences.
--
--   Differences from the source:
--   - encoding: Sⁿ with the Frobenius inner product → SunNLSDP.Equiv.SymMat (Fin n) (symmetric subspace of EuclideanSpace ℝ (Fin n × Fin n)); reason: its inherited inner product is Σ MᵢⱼNᵢⱼ, the Frobenius product
--   - encoding: functions with values in (−∞, +∞] → EReal-valued functions; θ(x̄), p(x) at points where they are finite enter as real numbers (toReal); reason: Lean convention; the values are finite at every such point (the subdifferential there is nonempty), so no instance changes
--   - encoding: ∂f(x), the convex-analysis subdifferential → subdiff f x, empty where f x is not finite; reason: standard convention for proper functions; ∂f(x) = ∅ off dom f
--   - encoding: N_D(x), defined for x ∈ D → normalCone D x, empty for x ∉ D; reason: the convention N_D = ∂δ_D; the source only uses N_D(x) at x ∈ D or through ∂δ_D
--   - encoding: polyhedral convex set → finite intersection of half-spaces {z | φᵢ z ≤ βᵢ} with φᵢ linear functionals (IsPolyhedral); reason: the standard definition; the empty set and the whole space are included
--   - reading: Suppose that S̄ and X̄ have eigenvalue decompositions as in (16) → not a hypothesis; |α|, |β|, |γ| counted from the eigenvalues of X̄ − S̄; reason: under the other hypotheses X̄S̄ = 0, so (16) always exists; the clause fixes notation
--   - encoding: |γ| ≥ n − 1 with n − 1 an integer → (n : ℤ) − 1 ≤ |γ|; reason: avoids natural-number subtraction at n = 0
-- source:
--   Cui, Liang, Sun, Toh, On Degenerate Doubly Nonnegative Projection Problems, arXiv:2009.11272v2 (preprint basis), https://arxiv.org/abs/2009.11272v2, Proposition 7, p.11

import Mathlib
import Definitions.Def_DNNProj_Basics
import Definitions.Def_DNNProj_DNN

open scoped RealInnerProductSpace

namespace DNNProj

/-- **Proposition 7** (Cui–Liang–Sun–Toh, arXiv:2009.11272v2, p.11). Let `S̄ ∈ Sⁿ₊` and
`0 ∈ X̄ + ∂δ_{Sⁿ₊}(S̄)`, and let `α, β, γ` be the index sets (15) of the eigenvalues of
`Z̄ = X̄ − S̄`. Then
(a) `N_{Sⁿ₊}(S̄)` is a polyhedral set if and only if `|γ| ≥ n − 1`;
(b) `0 ∈ X̄ + ri(N_{Sⁿ₊}(S̄))` if and only if `|β| = 0`, i.e., `rank(X̄) + rank(S̄) = n`.

**Formalization Note.** `0 ∈ X̄ + ∂δ(S̄)` is `−X̄ ∈ ∂δ_{Sⁿ₊}(S̄)`, and `0 ∈ X̄ + ri N` is
`−X̄ ∈ ri N`. `N_{Sⁿ₊}(S̄) ⊆ Sⁿ` is polyhedral as a subset of `Sⁿ`, and `ri` is
`intrinsicInterior ℝ` in `Sⁿ`. "`S̄` and `X̄` have eigenvalue decompositions as in (16)" always
holds under the hypotheses (they commute, `X̄S̄ = 0`), so it is not a hypothesis. `|γ| ≥ n − 1` is
compared in `ℤ`. Part (b) states both equivalences printed ("if and only if `|β| = 0`, i.e., …"). -/
theorem proposition_7 {n : ℕ} (Sbar Xbar : Sym n) (hS : Sbar ∈ psd n)
    (h0 : -Xbar ∈ subdiff (indicatorE (psd n)) Sbar) :
    (IsPolyhedral (normalCone (psd n) Sbar) ↔ (n : ℤ) - 1 ≤ (cardGamma Xbar Sbar : ℤ)) ∧
      ((-Xbar ∈ intrinsicInterior ℝ (normalCone (psd n) Sbar) ↔ cardBeta Xbar Sbar = 0) ∧
        (cardBeta Xbar Sbar = 0 ↔ (toMat Xbar).rank + (toMat Sbar).rank = n)) := by sorry

end DNNProj
