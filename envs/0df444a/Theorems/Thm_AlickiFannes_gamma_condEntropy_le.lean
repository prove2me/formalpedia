-- Prove2me | Theorems.Thm_AlickiFannes_gamma_condEntropy_le
-- name    : AlickiFannes.gamma_condEntropy_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:21:58.966732+00:00
-- url     : https://prove2.me/theorems/3c5031b6-b37a-4bfb-938b-aad6490b21a1
-- title:
--   $S(\gamma^{12}\mid\gamma^2) \le (1-\epsilon)(S(\rho^{12}) - S(\rho^2)) + \epsilon(S(\tilde\rho^{12}) - S(\tilde\rho^2)) + \eta(1-\epsilon) + \eta(\epsilon)$
-- statement:
--   Let $\mathfrak h^{12} = \mathfrak h_1 \otimes \mathfrak h_2$ be a finite-dimensional bipartite Hilbert space, $d_1 = \dim \mathfrak h_1$, and let $\rho^{12}, \tilde\rho^{12}$ be two states (density matrices) on $\mathfrak h^{12}$. For $0 \le \epsilon \le 1$ put $\gamma^{12} := (1-\epsilon)\rho^{12} + \epsilon\tilde\rho^{12}$, again a state. Write $\rho^2, \tilde\rho^2, \gamma^2$ for the restrictions to the second system (partial trace over $\mathfrak h_1$), $S$ for the von Neumann entropy, $S(\rho^{12}\mid\rho^2) = S(\rho^{12}) - S(\rho^2)$ for the conditional entropy, and $\eta(x) = -x\log x$ with $\eta(0) = 0$.
--
--   Then
--
--   $$
--   S(\gamma^{12}\mid\gamma^2) \;\le\; (1-\epsilon)\bigl(S(\rho^{12}) - S(\rho^2)\bigr) + \epsilon\bigl(S(\tilde\rho^{12}) - S(\tilde\rho^2)\bigr) + \eta(1-\epsilon) + \eta(\epsilon).
--   $$
--
--   The paper writes the display as $S(\gamma^{12}\mid\gamma^2) = S(\gamma^{12}) - S(\gamma^2) \le \dots$; the equality is the definition of the conditional entropy. The bound is the reverse of concavity of the conditional entropy, up to the binary-entropy term $\eta(1-\epsilon) + \eta(\epsilon)$.
--
--   Differences from the source:
--   - encoding: $\log$ of unspecified base in $S$, $\eta$ and $\log d_1$ → `Real.logb 2` throughout (`QAlgorithms.vnEntropy`, `AlickiFannes.eta`); reason: every term is one multiple of $\log$, so a common base gives the same statement.
--   - encoding: $\mathfrak h^{12} = \mathfrak h_1\otimes\mathfrak h_2$ finite dimensional, $\rho^2$ the restriction to system 2 → index type `A × B` with `A` $=\mathfrak h_1$, $\rho^2$ = `QAlgorithms.traceLeft ρ`, $\epsilon$ real and cast to $\mathbb C$ in the mixture; reason: Lean convention; the same states and the same restriction.
-- source:
--   Alicki–Fannes, Continuity of quantum conditional information, arXiv:quant-ph/0312081v2, proof of the Lemma, display "to obtain S(γ¹²| γ²) = …", p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_AlickiFannes_eta
import Definitions.Def_AlickiFannes_condEntropy

open QAlgorithms

namespace AlickiFannes

/-- Alicki–Fannes, arXiv:quant-ph/0312081v2, proof of the Lemma, p.3: "S(γ¹²| γ²) =
S(γ¹²) − S(γ²) ≤ (1 − ϵ)(S(ρ¹²) − S(ρ²)) + ϵ(S(ρ̃¹²) − S(ρ̃²)) + η(1 − ϵ) + η(ϵ)", for states `ρ¹²`, `ρ̃¹²` on `𝔥¹²`, `0 ≤ ϵ ≤ 1` and `γ¹² := (1 − ϵ) ρ¹² + ϵ ρ̃¹²`.
The equality in the display is the definition of `S(γ¹²| γ²)`; the inequality is stated.

**Formalization Note.** Here `𝔥¹² = 𝔥₁ ⊗ 𝔥₂` is the index type `A × B` (first factor `A` = `𝔥₁`,
traced out by `traceLeft`), states are density matrices (`QAlgorithms.IsDensityMatrix`: positive
semidefinite, trace one), the real weights `1 − ε`, `ε` are cast to `ℂ`, and `S`, `S(·|·)`, `η`
use the base-2 logarithm (`QAlgorithms.vnEntropy`, `AlickiFannes.condEntropy`,
`AlickiFannes.eta`). Both endpoints `ε = 0` and `ε = 1` are included, as on the page. The right-hand side is written with the entropies of the states
and of their restrictions to `𝔥₂` (`traceLeft`), as on the page. -/
theorem gamma_condEntropy_le {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ ρt : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) (hρt : IsDensityMatrix ρt)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    let γ := ((1 - ε : ℝ) : ℂ) • ρ + ((ε : ℝ) : ℂ) • ρt
    condEntropy γ ≤ (1 - ε) * (vnEntropy ρ - vnEntropy (traceLeft ρ)) +
      ε * (vnEntropy ρt - vnEntropy (traceLeft ρt)) + eta (1 - ε) + eta ε := by sorry

end AlickiFannes
