-- Prove2me | Theorems.Thm_ErschlerZheng_orbitKernel_muBeta_eq_zero_of_orbitDist_eq_two
-- name    : ErschlerZheng.orbitKernel_muBeta_eq_zero_of_orbitDist_eq_two
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:16:11.419983+00:00
-- url     : https://prove2.me/theorems/9a7c2030-98f8-4a56-b04e-11f78be36123
-- title:
--   Supporting fact for Proposition 7.18, not in the paper — under Fr(D) and an admissible (k_n), P_{μ_β}(x, y) = 0 whenever d(x, y) = 2
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $(k_n)$ satisfy the standing assumption of p. 40 (`IsAdmissibleSeq`), and let $\beta$ be real. Let $P$ be the transition kernel induced by $\mu_\beta$ (`muBeta`) on the orbit $1^\infty \cdot G_\omega$ (`orbitKernel … oneRay`), and write $d(x, y)$ for the Schreier distance (`orbitDist`). Then $P(x, y) = 0$ for all $x, y$ in the orbit with $d(x, y) = 2$.
--
--   This is not a result of the paper. It backs the sentence of the note `orbitKernel_muBeta_le_and_tail_le` saying that $P_{\mu_\beta}$ vanishes at distance $2$.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 46, P_{μ_β} vanishes at Schreier distance 2 (supporting fact, not in the paper)

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

namespace ErschlerZheng

theorem orbitKernel_muBeta_eq_zero_of_orbitDist_eq_two (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (β : ℝ) (x y : orbitOne ω)
    (hxy : orbitDist ω x y = 2) :
    orbitKernel (grigorchuk ω) (muBeta D ω k β) oneRay x y = 0 := by
  sorry

end ErschlerZheng
