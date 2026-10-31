-- Prove2me | Theorems.Thm_AlickiFannes_entropy_mixture_le
-- name    : AlickiFannes.entropy_mixture_le
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:21:49.690256+00:00
-- url     : https://prove2.me/theorems/2538addd-ba4f-4b94-aeaf-104cf86035d4
-- title:
--   Mixture bound $S((1-\epsilon)\rho + \epsilon\tilde\rho) \le (1-\epsilon)S(\rho) + \epsilon S(\tilde\rho) + \eta(1-\epsilon) + \eta(\epsilon)$
-- statement:
--   Let $\rho, \tilde\rho$ be two states (density matrices) of a finite-dimensional quantum system, $0 \le \epsilon \le 1$, and $\eta(x) = -x\log x$ with $\eta(0) = 0$. Then
--
--   $$
--   S\bigl((1-\epsilon)\rho + \epsilon\tilde\rho\bigr) \;\le\; (1-\epsilon)\,S(\rho) + \epsilon\,S(\tilde\rho) + \eta(1-\epsilon) + \eta(\epsilon),
--   $$
--
--   where $S$ is the von Neumann entropy. Together with concavity of $S$ this says that the entropy of a two-state mixture exceeds the average entropy by at most the binary entropy of the weights. The paper applies it on $\mathfrak h^{12}$ to $\gamma^{12} = (1-\epsilon)\rho^{12} + \epsilon\tilde\rho^{12}$ (proof of the Lemma, p.3).
--
--   Differences from the source:
--   - generalization: the bound for states $\rho^{12}, \tilde\rho^{12}$ on $\mathfrak h^{12}$ → the same bound for any two states of any finite-dimensional system; reason: at the system $\mathfrak h^{12}$ it is the page's display.
--   - encoding: $\log$ of unspecified base in $S$ and $\eta$ → `Real.logb 2` (`QAlgorithms.vnEntropy`, `AlickiFannes.eta`); $\epsilon$ real and cast to $\mathbb C$ in the mixture; reason: every term is one multiple of $\log$, so a common base gives the same statement.
-- source:
--   Alicki–Fannes, Continuity of quantum conditional information, arXiv:quant-ph/0312081v2, proof of the Lemma, "the upper bound" display, p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_AlickiFannes_eta
import Definitions.Def_AlickiFannes_condEntropy

open QAlgorithms

namespace AlickiFannes

/-- Alicki–Fannes, arXiv:quant-ph/0312081v2, proof of the Lemma, p.3: "and the upper bound
S(γ¹²) ≤ (1 − ϵ) S(ρ¹²) + ϵ S(ρ̃¹²) + η(1 − ϵ) + η(ϵ)". Stated for any two states `ρ`, `ρ̃` of a
finite-dimensional system and `0 ≤ ϵ ≤ 1`:
`S((1 − ϵ) ρ + ϵ ρ̃) ≤ (1 − ϵ) S(ρ) + ϵ S(ρ̃) + η(1 − ϵ) + η(ϵ)`. The page applies it on `𝔥¹²`.

**Formalization Note.** The system is an arbitrary finite index type `ι`, states are density
matrices (`QAlgorithms.IsDensityMatrix`), `S` is `QAlgorithms.vnEntropy` and `η` is
`AlickiFannes.eta`, both with the base-2 logarithm, and the real weights are cast to `ℂ`. Both
endpoints `ϵ = 0`, `ϵ = 1` are included (`η(0) = 0`). -/
theorem entropy_mixture_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ ρt : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ) (hρt : IsDensityMatrix ρt)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    vnEntropy (((1 - ε : ℝ) : ℂ) • ρ + ((ε : ℝ) : ℂ) • ρt) ≤
      (1 - ε) * vnEntropy ρ + ε * vnEntropy ρt + eta (1 - ε) + eta ε := by sorry

end AlickiFannes
