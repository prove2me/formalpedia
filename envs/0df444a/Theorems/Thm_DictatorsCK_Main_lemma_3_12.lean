-- Prove2me | Theorems.Thm_DictatorsCK_Main_lemma_3_12
-- name    : DictatorsCK.Main.lemma_3_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:38:21.609801+00:00
-- url     : https://prove2.me/theorems/7f91e501-349d-455c-a965-37b2ebb8cd06
-- title:
--   Lemma 3.12 — odd-lift bound $W_1(f)+\mu^2\le\min\{\mathrm{KKh}(\max(\alpha,|\mu|)),\mathrm{QLP}(\alpha),\mathrm{QLP}(|\mu|)\}$ and the cap $193027/250000$
-- statement:
--   Let $n\ge1$, let $f:\{-1,1\}^n\to\{-1,1\}$ have mean $\mu$, put $\alpha=\max_i|\hat f(i)|$ and $W_1(f)=\sum_i\hat f(i)^2$. With $\mathrm{QLP}$ and $\mathrm{KKh}$ as in (3.5), (3.6),
--   $$W_1(f)+\mu^2\le\min\big\{\mathrm{KKh}(\max(\alpha,|\mu|)),\ \mathrm{QLP}(\alpha),\ \mathrm{QLP}(|\mu|)\big\}.$$
--   In particular, if $\max(\alpha,|\mu|)\le\frac{69}{100}$, then
--   $$W_1(f)+\mu^2<\frac{193027}{250000}.$$
--
--   This quadratic Fourier-energy bound handles the functions that neither entropy contraction (large $|\mu|$) nor the local criterion (large $\alpha$) covers at low correlation.
--
--   Differences from the source:
--   - encoding: the cube {−1, 1}^n and Boolean f : {−1, 1}^n → {−1, 1} → Cube n = Fin n → Bool with x_i = 1 ⇔ true (coord, signEncoding); a Boolean f is f : Cube n → Bool read through signEncoding (true ↦ 1, false ↦ −1); reason: the cube type of the referenced goal; a relabelling of points and values that changes no instance
--   - encoding: max_{i∈[n]} |f̂(i)| → maxSingleton f = ⨆ i : Fin n, |f̂(i)|; reason: n ≥ 1, and the real supremum of finitely many values is their maximum
-- source:
--   Ky, Tran, Dictators are most informative, arXiv:2609.24184 (held copy, sha256 aa2515fb…0a2c7f), p. 17 (PDF 18), Lemma 3.12

import Mathlib
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_DictatorsCK_Main_Fourier
import Definitions.Def_DictatorsCK_Main_Information

open OAI.LeanBlast.CourtadeKumar

namespace DictatorsCK.Main

theorem lemma_3_12 {n : ℕ} (hn : 1 ≤ n) (f : Cube n → Bool) :
    levelWeight (signEncoding f) 1 + mean f ^ 2 ≤
        min (KKh (max (maxSingleton f) |mean f|)) (min (QLP (maxSingleton f)) (QLP |mean f|)) ∧
    (max (maxSingleton f) |mean f| ≤ 69 / 100 →
      levelWeight (signEncoding f) 1 + mean f ^ 2 < 193027 / 250000) := by sorry

end DictatorsCK.Main
