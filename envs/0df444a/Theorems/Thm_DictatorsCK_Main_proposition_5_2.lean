-- Prove2me | Theorems.Thm_DictatorsCK_Main_proposition_5_2
-- name    : DictatorsCK.Main.proposition_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:38:22.443495+00:00
-- url     : https://prove2.me/theorems/829ff464-c27c-4fc7-a68f-1d2301ad1289
-- title:
--   Proposition 5.2 — conditional Harris bounds on $W_2$ for increasing $f$, with one and with two retained coordinates
-- statement:
--   Let $n\ge1$, let $f:\{-1,1\}^n\to\{-1,1\}$ be increasing with $\mu=\mathbb E f$, and write $W_k=W_k(f)$, $\hat f(S)=\mathbb E[f\chi_S]$. For every $0<\eta\le1$,
--   $$\eta(1+\eta)W_2\le(1-\eta^2)W_1+\eta^2(1-\mu^2)-\hat f(1)^2.$$
--   If $n\ge2$, then also
--   $$\eta(1+\eta)W_2\le(1-\eta^2)W_1+\eta^2(1-\mu^2)-\hat f(1)^2-\hat f(2)^2+\eta\hat f(\{1,2\})^2\le(1-\eta^2)W_1+\eta^2-\hat f(1)^2-(1-\eta)\hat f(2)^2.$$
--   Coordinates $1$ and $2$ are fixed labels; no ordering of the coefficients is assumed.
--
--   These are the constraints on the second Fourier level that feed the cubic energy bound at intermediate correlations.
--
--   Differences from the source:
--   - encoding: the cube {−1, 1}^n and Boolean f : {−1, 1}^n → {−1, 1} → Cube n = Fin n → Bool with x_i = 1 ⇔ true (coord, signEncoding); a Boolean f is f : Cube n → Bool read through signEncoding (true ↦ 1, false ↦ −1); reason: the cube type of the referenced goal; a relabelling of points and values that changes no instance
--   - encoding: increasing: f(x) ≤ f(y) whenever x_i ≤ y_i for all i → IsIncreasing (signEncoding f), with the Bool order false < true; reason: false ↦ −1 < true ↦ 1, so the coordinate orders agree
--   - encoding: coordinates 1 and 2, and the coefficient f̂({1, 2}) → Fin indices 0 and 1 (⟨0, _⟩, ⟨1, _⟩), and fourierCoeff on {0, 1}; reason: index shift only
--   - encoding: the chain A ≤ B ≤ C of the second display → the conjunction A ≤ B ∧ B ≤ C; reason: a chain of inequalities asserts each link
-- source:
--   Ky, Tran, Dictators are most informative, arXiv:2609.24184 (held copy, sha256 aa2515fb…0a2c7f), p. 26–27 (PDF 27–28), Proposition 5.2

import Mathlib
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_DictatorsCK_Main_Fourier
import Definitions.Def_DictatorsCK_Main_Information

open OAI.LeanBlast.CourtadeKumar

namespace DictatorsCK.Main

theorem proposition_5_2 {n : ℕ} (hn : 1 ≤ n) (f : Cube n → Bool)
    (hf : IsIncreasing (signEncoding f)) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    η * (1 + η) * levelWeight (signEncoding f) 2 ≤
        (1 - η ^ 2) * levelWeight (signEncoding f) 1 + η ^ 2 * (1 - mean f ^ 2) -
          singletonCoeff (signEncoding f) ⟨0, by omega⟩ ^ 2 ∧
    ∀ hn2 : 2 ≤ n,
      η * (1 + η) * levelWeight (signEncoding f) 2 ≤
          (1 - η ^ 2) * levelWeight (signEncoding f) 1 + η ^ 2 * (1 - mean f ^ 2) -
            singletonCoeff (signEncoding f) ⟨0, by omega⟩ ^ 2 -
            singletonCoeff (signEncoding f) ⟨1, by omega⟩ ^ 2 +
            η * fourierCoeff (signEncoding f) {⟨0, by omega⟩, ⟨1, by omega⟩} ^ 2 ∧
      (1 - η ^ 2) * levelWeight (signEncoding f) 1 + η ^ 2 * (1 - mean f ^ 2) -
            singletonCoeff (signEncoding f) ⟨0, by omega⟩ ^ 2 -
            singletonCoeff (signEncoding f) ⟨1, by omega⟩ ^ 2 +
            η * fourierCoeff (signEncoding f) {⟨0, by omega⟩, ⟨1, by omega⟩} ^ 2 ≤
        (1 - η ^ 2) * levelWeight (signEncoding f) 1 + η ^ 2 -
          singletonCoeff (signEncoding f) ⟨0, by omega⟩ ^ 2 -
          (1 - η) * singletonCoeff (signEncoding f) ⟨1, by omega⟩ ^ 2 := by sorry

end DictatorsCK.Main
