-- Prove2me | Theorems.Thm_FTPLLinBandit_lemma_37
-- name    : FTPLLinBandit.lemma_37
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:02:45.624436+00:00
-- url     : https://prove2.me/theorems/b934db51-bfae-4ddc-b0b0-b62b8c0f1eff
-- title:
--   Lemma 37 — initial potential $\Psi_1(0)\le2R\sqrt{d\lambda}$
-- statement:
--   Let $d\ge1$, let $A\subseteq\mathbb R^d$ be nonempty with $A\subseteq RB^d_2$, and $\lambda>0$. Let $\rho_1=P_{\lambda I}$ be the Gaussian, radial-Laplace or Student-$t_2$ law of Tables 2 and 4. Then
--   $$\Psi_1(0)=\mathbb E_{Z\sim\rho_1}\Big[\max_{a\in A}\langle a,Z\rangle\Big]\le2R\sqrt{d\lambda}.$$
--
--   This bounds the penalty term $\Psi_1(0)$ of the regret decomposition (10); with $\lambda$ from (22) it is the source of the $Rd^{3/4}\sqrt T$ term of Theorem 13.
--
--   Differences from the source:
--   - encoding: A ⊆ RB^d_2 (with A nonempty from the standing Assumption 1) and the standing d ≥ 1 → hypotheses A.Nonempty and 1 ≤ d; reason: the paper's standing assumptions (Assumption 1 gives rB ⊆ conv A, so A ≠ ∅); for empty A Lean's sSup ∅ = 0 would make the support function 0
-- source:
--   Wei, Follow the Perturbed Leader for Linear Bandits: √T Regret over General Action Sets, arXiv:2610.17818, Lemma 37, p.47

import Mathlib
import Definitions.Def_FTPLLinBandit_radialFn
import Definitions.Def_FTPLLinBandit_ellDens
import Definitions.Def_FTPLLinBandit_potential

namespace FTPLLinBandit

/-- **Lemma 37 (Initial potential).** Wei, arXiv:2610.17818, Lemma 37, p.47: "Suppose A ⊆ RB^d_2
and λ > 0. Let ρ₁ = P_{λI} be any of the Gaussian, radial-Laplace, or Student-t₂ laws in Tables 2
and 4. Then Ψ₁(0) ≤ 2R√(dλ)."

For `d ≥ 1`, nonempty `A ⊆ R·B^d_2`, `λ > 0` and each of the three profiles `f`,
`Ψ₁(0) = E_{Z∼P_{λI}}[h_A(Z)] ≤ 2R√(dλ)`.

**Formalization Note.** `A` nonempty is the standing assumption (Assumption 1 gives
`rB^d_2 ⊆ conv(A)`); without it Lean's `sSup ∅ = 0` would make `h_A = 0`. `d ≥ 1` is the paper's
standing dimension assumption. -/
theorem lemma_37 {d : ℕ} (hd : 1 ≤ d) (A : Set (EuclideanSpace ℝ (Fin d))) (R : ℝ)
    (hA : A.Nonempty) (hAR : A ⊆ Metric.closedBall 0 R) (lam : ℝ) (hlam : 0 < lam)
    (f : RadialProfile) :
    potential A (ellDens (radialFn d f) (lam • (1 : Matrix (Fin d) (Fin d) ℝ))) 0 ≤
      2 * R * Real.sqrt (d * lam) := by sorry

end FTPLLinBandit
