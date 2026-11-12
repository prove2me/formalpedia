-- Prove2me | Theorems.Thm_DictatorsCK_Main_lemma_3_2
-- name    : DictatorsCK.Main.lemma_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:38:23.672878+00:00
-- url     : https://prove2.me/theorems/5d6bc8a6-0258-45f3-9add-af13e80429c3
-- title:
--   Lemma 3.2 — entropy contraction $\mathrm{Ent}(T_\eta f)\le\eta^2\mathrm{Ent}(f)$ and the posterior-entropy bound
-- statement:
--   Let $n\ge1$ and $0\le\eta\le1$, with $T_\eta$ the noise operator on the uniform cube and $H(t)=H_b((1-t)/2)$ the sign entropy in nats.
--
--   1. For every $f:\{-1,1\}^n\to[0,\infty)$, with $\mathrm{Ent}(f)=\mathbb E[f\log f]-\mathbb E f\log\mathbb E f$ ($0\log0=0$),
--   $$\mathrm{Ent}(T_\eta f)\le\eta^2\,\mathrm{Ent}(f).$$
--   2. Consequently, for every $g:\{-1,1\}^n\to[-1,1]$,
--   $$\mathbb E H(T_\eta g)\ge\eta^2\,\mathbb E H(g)+(1-\eta^2)H(\mathbb E g).$$
--
--   The second form is the information contraction $A_{\eta\rho}(f)\le\eta^2A_\rho(f)$ used to transport a bound at one correlation to every smaller one.
--
--   Differences from the source:
--   - encoding: real functions on the cube {−1, 1}^n → real functions on Cube n = Fin n → Bool with x_i = 1 ⇔ true; reason: the cube type of the referenced goal; a relabelling of points that changes no instance
-- source:
--   Ky, Tran, Dictators are most informative, arXiv:2609.24184 (held copy, sha256 aa2515fb…0a2c7f), p. 11 (PDF 12), Lemma 3.2

import Mathlib
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_DictatorsCK_Main_Fourier
import Definitions.Def_DictatorsCK_Main_Information

open OAI.LeanBlast.CourtadeKumar

namespace DictatorsCK.Main

theorem lemma_3_2 {n : ℕ} (hn : 1 ≤ n) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (∀ f : Cube n → ℝ, (∀ x, 0 ≤ f x) → ent (noiseOperator η f) ≤ η ^ 2 * ent f) ∧
    (∀ g : Cube n → ℝ, (∀ x, -1 ≤ g x ∧ g x ≤ 1) →
      η ^ 2 * cubeAverage (fun x => entropy (g x)) + (1 - η ^ 2) * entropy (cubeAverage g) ≤
        cubeAverage (fun x => entropy (noiseOperator η g x))) := by sorry

end DictatorsCK.Main
