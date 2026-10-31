-- Prove2me | Theorems.Thm_AlickiFannes_condEntropy_abs_le_log
-- name    : AlickiFannes.condEntropy_abs_le_log
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:10.635081+00:00
-- url     : https://prove2.me/theorems/a76d0a6b-351d-43e2-ab5c-b39884b53dfb
-- title:
--   $-\log d_1 \le S(\rho^{12}\mid\rho^2) \le \log d_1$ (used in (2))
-- statement:
--   Let $\mathfrak h^{12} = \mathfrak h_1 \otimes \mathfrak h_2$ be a finite-dimensional bipartite Hilbert space, $d_1 = \dim\mathfrak h_1$, and $\rho^{12}$ a state on $\mathfrak h^{12}$ with restriction $\rho^2$ to the second system. Then
--
--   $$
--   -\log d_1 \;\le\; S(\rho^{12}\mid\rho^2) \;\le\; \log d_1 .
--   $$
--
--   The bound depends only on the dimension of the first factor, the one that is traced out to form $\rho^2$, and not on $\dim \mathfrak h_2$. The paper uses it without stating it in the second inequality of (2), p.3, where $\epsilon\,(S(\rho^{12}\mid\rho^2) - S(\tilde\rho^{12}\mid\tilde\rho^2))$ is bounded by $2\epsilon\log d_1$; that difference bound follows from the two clauses applied to $\rho^{12}$ and $\tilde\rho^{12}$.
--
--   Differences from the source:
--   - generalization: (2) uses $\epsilon\,(S(\rho^{12}\mid\rho^2) - S(\tilde\rho^{12}\mid\tilde\rho^2)) \le 2\epsilon\log d_1$ → a two-sided bound $-\log d_1 \le S(\rho^{12}\mid\rho^2) \le \log d_1$ for every single state; reason: the paper's step follows from it at once ($\epsilon \ge 0$), and it is the fact the step uses.
--   - encoding: $\log$ of unspecified base in $S$ and $\log d_1$ → `Real.logb 2` throughout (`QAlgorithms.vnEntropy`); reason: every term is one multiple of $\log$, so a common base gives the same statement.
--   - encoding: $\mathfrak h^{12} = \mathfrak h_1\otimes\mathfrak h_2$ finite dimensional, $\rho^2$ the restriction to system 2 → index type `A × B` with `A` $=\mathfrak h_1$, $\rho^2$ = `QAlgorithms.traceLeft ρ`, $\epsilon$ real and cast to $\mathbb C$ in the mixture; reason: Lean convention; the same states and the same restriction.
-- source:
--   Alicki–Fannes, Continuity of quantum conditional information, arXiv:quant-ph/0312081v2, second inequality of eq. (2), p.3 (used there, not stated)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_AlickiFannes_eta
import Definitions.Def_AlickiFannes_condEntropy

open QAlgorithms

namespace AlickiFannes

/-- Alicki–Fannes, arXiv:quant-ph/0312081v2, second inequality of (2), p.3: the step
"ϵ (S(ρ¹²| ρ²) − S(ρ̃¹²| ρ̃²)) ≤ 2ϵ log d₁" uses, without stating it, that the conditional
entropy of every state of `𝔥¹²` lies between `−log d₁` and `log d₁`, where `d₁` is the dimension
of `𝔥₁` (the first, traced-out factor). This theorem states that per-state bound:
`−log d₁ ≤ S(ρ¹²| ρ²) ≤ log d₁`.

**Formalization Note.** `𝔥¹² = 𝔥₁ ⊗ 𝔥₂` is the index type `A × B`, `d₁ = Fintype.card A`, the
logarithm is base 2 (as in `QAlgorithms.vnEntropy`), and `ρ` is a density matrix
(`QAlgorithms.IsDensityMatrix`). No density matrix exists when `A` or `B` is empty. -/
theorem condEntropy_abs_le_log {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (ρ : Matrix (A × B) (A × B) ℂ) (hρ : IsDensityMatrix ρ) :
    -Real.logb 2 (Fintype.card A) ≤ condEntropy ρ ∧
      condEntropy ρ ≤ Real.logb 2 (Fintype.card A) := by sorry

end AlickiFannes
