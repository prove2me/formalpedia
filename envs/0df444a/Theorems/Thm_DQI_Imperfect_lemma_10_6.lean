-- Prove2me | Theorems.Thm_DQI_Imperfect_lemma_10_6
-- name    : DQI.Imperfect.lemma_10_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:03:36.613777+00:00
-- url     : https://prove2.me/theorems/c90639ff-1af5-4f1b-ada1-8d16ea5af2d5
-- title:
--   Lemma 10.6 — average matrix with decoding failures
-- statement:
--   For a binary matrix $B$, a fixed deterministic syndrome decoder, and $\ell\le m$, average the imperfect-decoder objective matrix over uniform $v\in\mathbb F_2^m$. Then
--
--   $$
--   \mathbb E_v\bar A^{(m,\ell,D)}=A^{(m,\ell,0)}-E^{(m,\ell,F)}.
--   $$
--
--   Here the $(k,k')$ entry of $E^{(m,\ell,F)}$ counts, for each coordinate $i$, the pairs in $(E_k\times F_{k'})\cup(F_k\times E_{k'})$ with $y+y'+e_i=0$, divided by $\sqrt{\binom m k\binom m{k'}}$. The matrix records the effect of misidentified errors on the averaged observable.
--
--   **Formalization Note** The same decoder is used at every $v$; the uniform average is over all $2^m$ phase vectors.
-- source:
--   Jordan et al., Optimization by Decoded Quantum Interferometry, arXiv:2408.08292v5, p. 41, Lemma 10.6, (180)–(182)

import Mathlib
import Definitions.Def_DQI_Imperfect_Setting

namespace DQI.Imperfect

theorem lemma_10_6 (m n ℓ : ℕ) (hℓ : ℓ ≤ m)
    (B : Matrix (Fin m) (Fin n) (ZMod 2)) (dec : (Fin n → ZMod 2) → (Fin m → ZMod 2)) :
    ((1 / ((2 : ℝ) ^ m)) •
      (∑ v : Fin m → ZMod 2, AbarD B v dec ℓ)) =
      DQI.Semicircle.Atri m ℓ 0 - Emat B dec ℓ := by sorry

end DQI.Imperfect
