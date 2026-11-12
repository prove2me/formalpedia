-- Prove2me | Theorems.Thm_DictatorsCK_Main_lemma_6_1
-- name    : DictatorsCK.Main.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:43:29.81573+00:00
-- url     : https://prove2.me/theorems/f16c7fd7-0388-42b3-9aff-a2ed55397a31
-- title:
--   Lemma 6.1 — sharp scalar estimate $(\arcsin t-\frac{\pi}{2}t)^2\le C_*\Psi(t)$ with optimal $C_*$, and its $L^2$ form
-- statement:
--   Let $\Psi(t)=t^2\log2-\Phi(t)$ and $C_*=\dfrac{(\pi/2-1)^2}{\log2-1/2}$.
--
--   1. For every $t\in[-1,1]$,
--   $$\Big(\arcsin t-\frac{\pi}{2}t\Big)^2\le C_*\Psi(t).$$
--   2. The constant $C_*$ is optimal: every constant $C$ for which the inequality holds for all $t\in[-1,1]$ satisfies $C\ge C_*$.
--   3. In the setting of Section 6 — $n\ge1$, $f:\{-1,1\}^n\to\{-1,1\}$ nonconstant, $0<\rho<1$, $g=T_\rho f$, $h=\arcsin g$, $J=\mathbb E\Psi(g)$ —
--   $$\Big\|h-\frac{\pi}{2}g\Big\|_2^2=\mathbb E\Big(h-\frac{\pi}{2}g\Big)^2\le C_*J.$$
--
--   This controls the error of replacing the arcsine transform of a noisy function by a multiple of the function itself, in terms of how far its entropy is above the quadratic lower bound.
--
--   Differences from the source:
--   - encoding: the cube {−1, 1}^n and Boolean f : {−1, 1}^n → {−1, 1} → Cube n = Fin n → Bool with x_i = 1 ⇔ true (coord, signEncoding); a Boolean f is f : Cube n → Bool read through signEncoding (true ↦ 1, false ↦ −1); reason: the cube type of the referenced goal; a relabelling of points and values that changes no instance
--   - encoding: “The constant C_* is optimal” → ∀ C, (∀ t ∈ [−1, 1], (arcsin t − (π/2)t)^2 ≤ C·Ψ(t)) → C_* ≤ C; reason: optimal means that no smaller constant makes the inequality hold on [−1, 1]
-- source:
--   Ky, Tran, Dictators are most informative, arXiv:2609.24184 (held copy, sha256 aa2515fb…0a2c7f), p. 32 (PDF 33), Lemma 6.1, (6.2)

import Mathlib
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_DictatorsCK_Main_Fourier
import Definitions.Def_DictatorsCK_Main_Information
import Definitions.Def_DictatorsCK_Main_Profile
import Definitions.Def_DictatorsCK_Main_Arcsine

open OAI.LeanBlast.CourtadeKumar

namespace DictatorsCK.Main

theorem lemma_6_1 :
    (∀ t : ℝ, -1 ≤ t → t ≤ 1 → (Real.arcsin t - Real.pi / 2 * t) ^ 2 ≤ Cstar * PsiGap t) ∧
    (∀ C : ℝ, (∀ t : ℝ, -1 ≤ t → t ≤ 1 → (Real.arcsin t - Real.pi / 2 * t) ^ 2 ≤ C * PsiGap t) →
      Cstar ≤ C) ∧
    (∀ (n : ℕ) (f : Cube n → Bool), IsNonconstant f → ∀ ρ : ℝ, 0 < ρ → ρ < 1 →
      cubeAverage (fun x => (Real.arcsin (noiseOperator ρ (signEncoding f) x) -
          Real.pi / 2 * noiseOperator ρ (signEncoding f) x) ^ 2) ≤
        Cstar * cubeAverage (fun x => PsiGap (noiseOperator ρ (signEncoding f) x))) := by sorry

end DictatorsCK.Main
