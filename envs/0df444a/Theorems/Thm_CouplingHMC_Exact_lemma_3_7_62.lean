-- Prove2me | Theorems.Thm_CouplingHMC_Exact_lemma_3_7_62
-- name    : CouplingHMC.Exact.lemma_3_7_62
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:28:09.151358+00:00
-- url     : https://prove2.me/theorems/1ef07f23-9cdb-4f95-a515-d559d4a0b477
-- title:
--   Lemma 3.7, (62), p. 22 — P[ξ − η ≠ −γz] ≤ |γz|/√(2π)
-- statement:
--   Let $\gamma>0$, $z\in\mathbb R^d$, $\xi\sim N(0,I_d)$ and, independently, $\tilde{\mathcal U}\sim\mathrm{Unif}(0,1)$, and let $\eta$ be defined from $(\xi,\tilde{\mathcal U})$ by (21): $\eta=\xi+\gamma z$ if $\tilde{\mathcal U}\le\varphi_{0,1}(e\cdot\xi+\gamma|z|)/\varphi_{0,1}(e\cdot\xi)$, and $\eta=\xi-2(e\cdot\xi)e$ otherwise, with $e=z/|z|$. Then
--
--   $$P[\xi-\eta\ne-\gamma z]\le\frac{|\gamma z|}{\sqrt{2\pi}}.$$
--
--   The coupling fails to realize the contractive velocity shift only with probability of order $\gamma|z|$.
--
--   **Formalization Note.** The bound is stated for every $z$, not only for $|z|<2\mathcal R$ where the paper applies it. The paper's (63)–(64) are not included.
-- source:
--   Bou-Rabee, Eberle, Zimmer, Coupling and convergence for Hamiltonian Monte Carlo, arXiv:1805.00452v2, Lemma 3.7, (62), p. 22, with (21), p. 8

import Mathlib
import Definitions.Def_CouplingHMC_Exact_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace CouplingHMC.Exact

/-- Lemma 3.7, (62) (p. 22): for every `γ > 0` and `z`, with `η` given by (21),
`P[ξ - η ≠ -γz] ≤ |γz|/√(2π)`. -/
theorem lemma_3_7_62 {d : ℕ} (γ : ℝ) (hγ : 0 < γ) (z : E d) :
    noiseLaw d {ω | ω.1 - reflEta γ z ω.1 ω.2 ≠ -(γ • z)} ≤
      ENNReal.ofReal (γ * ‖z‖ / Real.sqrt (2 * Real.pi)) := by sorry

end CouplingHMC.Exact
