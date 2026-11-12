-- Prove2me | Theorems.Thm_DictatorsCK_Main_lemma_7_2
-- name    : DictatorsCK.Main.lemma_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:34:57.630958+00:00
-- url     : https://prove2.me/theorems/a89a565b-85cb-4110-bc8c-fc2000276cc6
-- title:
--   Lemma 7.2 — martingale energy: affine and logarithmic lower bounds on $\mathrm{Dir}(h-P_Kh)$
-- statement:
--   Let $n\ge1$, $h:\{-1,1\}^n\to\mathbb R$ and $K\subseteq[n]$. Put $V=\|h-P_Kh\|_2^2=\mathbb E(h-P_Kh)^2$ and $b_K=\sum_{i\notin K}(\mathbb E|\partial_ih|)^2$. For every $\lambda\in\mathbb R$,
--   $$\mathrm{Dir}(h-P_Kh)\ge\Big(1+\frac{\lambda}{2}\Big)V-\frac{e^{\lambda-1}}{2}\,b_K.$$
--   If $V,b_K>0$, then also
--   $$\mathrm{Dir}(h-P_Kh)\ge V+\frac V2\log\frac{V}{b_K}.$$
--
--   The bound improves on the Poincaré inequality for the energy outside a coordinate projection when the outside influences are small.
--
--   Differences from the source:
--   - encoding: real functions on the cube {−1, 1}^n → real functions on Cube n = Fin n → Bool with x_i = 1 ⇔ true; reason: the cube type of the referenced goal; a relabelling of points that changes no instance
--   - encoding: coordinates i ∈ [n] = {1, …, n} → i : Fin n = {0, …, n − 1}; reason: index shift only
--   - encoding: ∂_i h as a function on {−1, 1}^{[n]∖{i}} → halfDiff i h on the full cube, ignoring x_i; reason: the paper itself views ∂_i h this way (p. 9); its norms and expectations are unchanged
-- source:
--   Ky, Tran, Dictators are most informative, arXiv:2609.24184 (held copy, sha256 aa2515fb…0a2c7f), p. 37 (PDF 38), Lemma 7.2

import Mathlib
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_DictatorsCK_Main_Fourier

open OAI.LeanBlast.CourtadeKumar

namespace DictatorsCK.Main

theorem lemma_7_2 {n : ℕ} (hn : 1 ≤ n) (h : Cube n → ℝ) (K : Finset (Fin n)) :
    (∀ lam : ℝ,
      (1 + lam / 2) * cubeAverage (fun x => (h x - proj K h x) ^ 2) -
          Real.exp (lam - 1) / 2 * ∑ i ∈ Kᶜ, cubeAverage (fun x => |halfDiff i h x|) ^ 2 ≤
        dirichlet (fun x => h x - proj K h x)) ∧
    (0 < cubeAverage (fun x => (h x - proj K h x) ^ 2) →
      0 < ∑ i ∈ Kᶜ, cubeAverage (fun x => |halfDiff i h x|) ^ 2 →
      cubeAverage (fun x => (h x - proj K h x) ^ 2) +
          cubeAverage (fun x => (h x - proj K h x) ^ 2) / 2 *
            Real.log (cubeAverage (fun x => (h x - proj K h x) ^ 2) /
              ∑ i ∈ Kᶜ, cubeAverage (fun x => |halfDiff i h x|) ^ 2) ≤
        dirichlet (fun x => h x - proj K h x)) := by sorry

end DictatorsCK.Main
