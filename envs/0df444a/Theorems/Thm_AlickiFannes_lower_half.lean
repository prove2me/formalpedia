-- Prove2me | Theorems.Thm_AlickiFannes_lower_half
-- name    : AlickiFannes.lower_half
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:11.304287+00:00
-- url     : https://prove2.me/theorems/23871b78-0969-4f6a-9b84-9a99fd62fe2f
-- title:
--   Eq. (3): $S(\rho^{12}\mid\rho^2) - S(\gamma^{12}\mid\gamma^2) \ge -2\epsilon\log d_1 - \eta(1-\epsilon) - \eta(\epsilon)$ (both inequalities of the chain)
-- statement:
--   Let $\mathfrak h^{12} = \mathfrak h_1 \otimes \mathfrak h_2$ be a finite-dimensional bipartite Hilbert space, $d_1 = \dim \mathfrak h_1$, and let $\rho^{12}, \tilde\rho^{12}$ be two states (density matrices) on $\mathfrak h^{12}$. For $0 \le \epsilon \le 1$ put $\gamma^{12} := (1-\epsilon)\rho^{12} + \epsilon\tilde\rho^{12}$, again a state. Write $\rho^2, \tilde\rho^2, \gamma^2$ for the restrictions to the second system (partial trace over $\mathfrak h_1$), $S$ for the von Neumann entropy, $S(\rho^{12}\mid\rho^2) = S(\rho^{12}) - S(\rho^2)$ for the conditional entropy, and $\eta(x) = -x\log x$ with $\eta(0) = 0$.
--
--   Then both inequalities of the chain (3) hold:
--
--   1. $$S(\rho^{12}\mid\rho^2) - S(\gamma^{12}\mid\gamma^2) \;\ge\; \epsilon\,\bigl(S(\rho^{12}\mid\rho^2) - S(\tilde\rho^{12}\mid\tilde\rho^2)\bigr) - \eta(1-\epsilon) - \eta(\epsilon),$$
--   2. $$S(\rho^{12}\mid\rho^2) - S(\gamma^{12}\mid\gamma^2) \;\ge\; -2\epsilon\log d_1 - \eta(1-\epsilon) - \eta(\epsilon).$$
--
--   This is the lower half of the Lemma: mixing in a fraction $\epsilon$ of another state can raise the conditional entropy by at most $2\epsilon\log d_1 + \eta(1-\epsilon) + \eta(\epsilon)$.
--
--   Differences from the source:
--   - encoding: $\log$ of unspecified base in $S$, $\eta$ and $\log d_1$ → `Real.logb 2` throughout (`QAlgorithms.vnEntropy`, `AlickiFannes.eta`); reason: every term is one multiple of $\log$, so a common base gives the same statement.
--   - encoding: $\mathfrak h^{12} = \mathfrak h_1\otimes\mathfrak h_2$ finite dimensional, $\rho^2$ the restriction to system 2 → index type `A × B` with `A` $=\mathfrak h_1$, $\rho^2$ = `QAlgorithms.traceLeft ρ`, $\epsilon$ real and cast to $\mathbb C$ in the mixture; reason: Lean convention; the same states and the same restriction.
-- source:
--   Alicki–Fannes, Continuity of quantum conditional information, arXiv:quant-ph/0312081v2, eq. (3), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_AlickiFannes_eta
import Definitions.Def_AlickiFannes_condEntropy

open QAlgorithms

namespace AlickiFannes

/-- Alicki–Fannes, arXiv:quant-ph/0312081v2, eq. (3), p.3: for states `ρ¹²`, `ρ̃¹²` on `𝔥¹²`, `0 ≤ ϵ ≤ 1` and `γ¹² := (1 − ϵ) ρ¹² + ϵ ρ̃¹²`,
"S(ρ¹²| ρ²) − S(γ¹²| γ²) ≥ ϵ (S(ρ¹²| ρ²) − S(ρ̃¹²| ρ̃²)) − η(1 − ϵ) − η(ϵ)
≥ −2ϵ log d₁ − η(1 − ϵ) − η(ϵ)", with `d₁` the dimension of `𝔥₁`. Both inequalities of the
chain are stated, as two conjuncts with the common right-hand side `S(ρ¹²| ρ²) − S(γ¹²| γ²)`.

**Formalization Note.** Here `𝔥¹² = 𝔥₁ ⊗ 𝔥₂` is the index type `A × B` (first factor `A` = `𝔥₁`,
traced out by `traceLeft`), states are density matrices (`QAlgorithms.IsDensityMatrix`: positive
semidefinite, trace one), the real weights `1 − ε`, `ε` are cast to `ℂ`, and `S`, `S(·|·)`, `η`
use the base-2 logarithm (`QAlgorithms.vnEntropy`, `AlickiFannes.condEntropy`,
`AlickiFannes.eta`). Both endpoints `ε = 0` and `ε = 1` are included, as on the page. `d₁ = Fintype.card A`. -/
theorem lower_half {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ ρt : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) (hρt : IsDensityMatrix ρt)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    let γ := ((1 - ε : ℝ) : ℂ) • ρ + ((ε : ℝ) : ℂ) • ρt
    ε * (condEntropy ρ - condEntropy ρt) - eta (1 - ε) - eta ε ≤
        condEntropy ρ - condEntropy γ ∧
      -(2 * ε * Real.logb 2 (Fintype.card A)) - eta (1 - ε) - eta ε ≤
        condEntropy ρ - condEntropy γ := by sorry

end AlickiFannes
