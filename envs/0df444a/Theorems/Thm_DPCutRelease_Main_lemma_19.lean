-- Prove2me | Theorems.Thm_DPCutRelease_Main_lemma_19
-- name    : DPCutRelease.Main.lemma_19
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:12:36.778185+00:00
-- url     : https://prove2.me/theorems/a5e0c47e-6a1f-4f3b-b0b8-c7cf0c42d229
-- title:
--   Lemma 19 — the regularized objective F controls every integral cut
-- statement:
--   There is a universal constant $C>0$ such that for every $\lambda>0$, every signed vector $D\in\mathbb R^{\binom n2}$ and every cut $S\subseteq[n]$,
--   $$\langle D,c_S\rangle\le2\max\{F(D),0\}+C\Big(\lambda n\log n+\frac{\|D\|_1}n\Big).$$
--   Moreover, $\langle D,\mathbf 1\rangle\le2F(D)$. Here $F(D)=\max_{X\in\mathcal X}\{\langle D,q(X)\rangle+\lambda\log\det X\}$ (Eq. (4)). It turns a small value of $F$ into an all-cut accuracy certificate (Lemma 20).
--
--   **Formalization Note.** `Freg lam D`, `cutVec`, `l1`; $\mathbf 1$ is the all-ones vector.
--
--   Differences from the source:
--   - reading: "O(λ n log n + ‖D‖₁/n)" → C·(λ n log n + ‖D‖₁/n) with ∃ C > 0 universal, before n, λ, D; reason: O(·) is an explicit universal constant
--   - reading: λ of Eq. (4), positive throughout §3–§5 → hypothesis 0 < lam; reason: standing assumption of the section; F is defined through the maximizer, unique for λ > 0
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 27, Lemma 19

import Mathlib
import Definitions.Def_DPCutRelease_Main_EdgeDP
import Definitions.Def_DPCutRelease_Main_SDP

open MeasureTheory ProbabilityTheory Matrix

namespace DPCutRelease.Main

/-- Lemma 19 (p. 27): there is a universal `C` such that for every `λ > 0`, every `D` and every cut
`S ⊆ [n]`, `⟨D, c_S⟩ ≤ 2 max{F(D), 0} + C(λ n log n + ‖D‖₁/n)`; moreover `⟨D, 1⟩ ≤ 2F(D)`. -/
theorem lemma_19 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (lam : ℝ) (D : EdgeVec n), 0 < lam →
      (∀ S : Finset (Fin n), dot D (cutVec S) ≤
          2 * max (Freg lam D) 0 + C * (lam * n * Real.log n + l1 D / n)) ∧
        dot D 1 ≤ 2 * Freg lam D := by sorry

end DPCutRelease.Main
