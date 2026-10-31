-- Prove2me | Theorems.Thm_AlickiFannes_entropy_concave_two
-- name    : AlickiFannes.entropy_concave_two
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:21:56.638065+00:00
-- url     : https://prove2.me/theorems/3221d201-cbd7-4f82-b1ec-4b3581c8e080
-- title:
--   Concavity of the von Neumann entropy, $S((1-\epsilon)\rho + \epsilon\tilde\rho) \ge (1-\epsilon)S(\rho) + \epsilon S(\tilde\rho)$
-- statement:
--   Let $\rho, \tilde\rho$ be two states (density matrices) of a finite-dimensional quantum system and $0 \le \epsilon \le 1$. Then
--
--   $$
--   S\bigl((1-\epsilon)\rho + \epsilon\tilde\rho\bigr) \;\ge\; (1-\epsilon)\,S(\rho) + \epsilon\,S(\tilde\rho),
--   $$
--
--   where $S$ is the von Neumann entropy. In the proof of the Lemma (p.3) the paper uses it on the second system, $S(\gamma^2) \ge (1-\epsilon)S(\rho^2) + \epsilon S(\tilde\rho^2)$; there $\gamma^2 = (1-\epsilon)\rho^2 + \epsilon\tilde\rho^2$ because the partial trace is linear.
--
--   Differences from the source:
--   - generalization: $S(\gamma^2) \ge (1-\epsilon)S(\rho^2) + \epsilon S(\tilde\rho^2)$ for the restrictions to $\mathfrak h_2$ → the same inequality for any two states of any finite-dimensional system; reason: at the system $\mathfrak h_2$ with the states $\rho^2, \tilde\rho^2$ it is the page's display, since $\gamma^2 = (1-\epsilon)\rho^2 + \epsilon\tilde\rho^2$.
--   - encoding: $\log$ of unspecified base in $S$ → `Real.logb 2` (`QAlgorithms.vnEntropy`); $\epsilon$ real and cast to $\mathbb C$ in the mixture; reason: a positive multiple of the entropy, the inequality is unchanged.
-- source:
--   Alicki–Fannes, Continuity of quantum conditional information, arXiv:quant-ph/0312081v2, proof of the Lemma, "concavity of the entropy" display, p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_AlickiFannes_eta
import Definitions.Def_AlickiFannes_condEntropy

open QAlgorithms

namespace AlickiFannes

/-- Alicki–Fannes, arXiv:quant-ph/0312081v2, proof of the Lemma, p.3: "Next, we use the
concavity of the entropy S(γ²) ≥ (1 − ϵ) S(ρ²) + ϵ S(ρ̃²)". Stated for any two states `ρ`, `ρ̃`
of a finite-dimensional system and `0 ≤ ϵ ≤ 1`:
`S((1 − ϵ) ρ + ϵ ρ̃) ≥ (1 − ϵ) S(ρ) + ϵ S(ρ̃)`. The page applies it on `𝔥₂` to `ρ²`, `ρ̃²`,
whose mixture `(1 − ϵ) ρ² + ϵ ρ̃²` is the restriction `γ²` of `γ¹²` (the partial trace is linear).

**Formalization Note.** The system is an arbitrary finite index type `ι`, states are density
matrices (`QAlgorithms.IsDensityMatrix`), `S` is `QAlgorithms.vnEntropy` (base 2), and the real
weights are cast to `ℂ`. Both endpoints `ϵ = 0`, `ϵ = 1` are included. -/
theorem entropy_concave_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ ρt : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ) (hρt : IsDensityMatrix ρt)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1 - ε) * vnEntropy ρ + ε * vnEntropy ρt ≤
      vnEntropy (((1 - ε : ℝ) : ℂ) • ρ + ((ε : ℝ) : ℂ) • ρt) := by sorry

end AlickiFannes
