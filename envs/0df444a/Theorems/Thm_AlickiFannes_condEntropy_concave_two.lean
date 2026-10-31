-- Prove2me | Theorems.Thm_AlickiFannes_condEntropy_concave_two
-- name    : AlickiFannes.condEntropy_concave_two
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:21:50.375105+00:00
-- url     : https://prove2.me/theorems/8a6c26ab-88ec-4a22-9997-3899667b3789
-- title:
--   Concavity of the conditional entropy, $S(\gamma^{12}\mid\gamma^2) \ge (1-\epsilon)S(\rho^{12}\mid\rho^2) + \epsilon S(\tilde\rho^{12}\mid\tilde\rho^2)$
-- statement:
--   Let $\mathfrak h^{12} = \mathfrak h_1 \otimes \mathfrak h_2$ be a finite-dimensional bipartite Hilbert space, $d_1 = \dim \mathfrak h_1$, and let $\rho^{12}, \tilde\rho^{12}$ be two states (density matrices) on $\mathfrak h^{12}$. For $0 \le \epsilon \le 1$ put $\gamma^{12} := (1-\epsilon)\rho^{12} + \epsilon\tilde\rho^{12}$, again a state. Write $\rho^2, \tilde\rho^2, \gamma^2$ for the restrictions to the second system (partial trace over $\mathfrak h_1$), $S$ for the von Neumann entropy, $S(\rho^{12}\mid\rho^2) = S(\rho^{12}) - S(\rho^2)$ for the conditional entropy, and $\eta(x) = -x\log x$ with $\eta(0) = 0$.
--
--   The conditional entropy is concave:
--
--   $$
--   S(\gamma^{12}\mid\gamma^2) \;\ge\; (1-\epsilon)\,S(\rho^{12}\mid\rho^2) + \epsilon\,S(\tilde\rho^{12}\mid\tilde\rho^2).
--   $$
--
--   This is the first step of the proof of the Lemma on p.3; the paper does not prove it but cites W. Thirring, *Quantum Mathematical Physics* ([3]). It is equivalent to strong subadditivity of the von Neumann entropy.
--
--   Differences from the source:
--   - encoding: $\log$ of unspecified base in $S$ and $\log d_1$ → `Real.logb 2` throughout (`QAlgorithms.vnEntropy`); reason: every term is one multiple of $\log$, so a common base gives the same statement.
--   - encoding: $\mathfrak h^{12} = \mathfrak h_1\otimes\mathfrak h_2$ finite dimensional, $\rho^2$ the restriction to system 2 → index type `A × B` with `A` $=\mathfrak h_1$, $\rho^2$ = `QAlgorithms.traceLeft ρ`, $\epsilon$ real and cast to $\mathbb C$ in the mixture; reason: Lean convention; the same states and the same restriction.
-- source:
--   Alicki–Fannes, Continuity of quantum conditional information, arXiv:quant-ph/0312081v2, proof of the Lemma, first display, p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_AlickiFannes_eta
import Definitions.Def_AlickiFannes_condEntropy

open QAlgorithms

namespace AlickiFannes

/-- Alicki–Fannes, arXiv:quant-ph/0312081v2, proof of the Lemma, first display, p.3: "As the
conditional entropy is concave, see [3], we have
S(γ¹²| γ²) ≥ (1 − ϵ) S(ρ¹²| ρ²) + ϵ S(ρ̃¹²| ρ̃²)", for states `ρ¹²`, `ρ̃¹²` on `𝔥¹²`, `0 ≤ ϵ ≤ 1` and `γ¹² := (1 − ϵ) ρ¹² + ϵ ρ̃¹²`. The paper does not prove this; it
cites W. Thirring's *Quantum Mathematical Physics* ([3]).

**Formalization Note.** Here `𝔥¹² = 𝔥₁ ⊗ 𝔥₂` is the index type `A × B` (first factor `A` = `𝔥₁`,
traced out by `traceLeft`), states are density matrices (`QAlgorithms.IsDensityMatrix`: positive
semidefinite, trace one), the real weights `1 − ε`, `ε` are cast to `ℂ`, and `S`, `S(·|·)`, `η`
use the base-2 logarithm (`QAlgorithms.vnEntropy`, `AlickiFannes.condEntropy`,
`AlickiFannes.eta`). Both endpoints `ε = 0` and `ε = 1` are included, as on the page. -/
theorem condEntropy_concave_two {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ρ ρt : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) (hρt : IsDensityMatrix ρt)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    let γ := ((1 - ε : ℝ) : ℂ) • ρ + ((ε : ℝ) : ℂ) • ρt
    (1 - ε) * condEntropy ρ + ε * condEntropy ρt ≤ condEntropy γ := by sorry

end AlickiFannes
