-- Prove2me | Theorems.Thm_Bartholdi_card_wordBall_le_exp_mul_rpow_alpha0
-- name    : Bartholdi.card_wordBall_le_exp_mul_rpow_alpha0
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T10:57:31.553647+00:00
-- url     : https://prove2.me/theorems/87cf1ba3-ec17-470a-af45-1bb8056fd530
-- title:
--   Bartholdi; Muchnik–Pak, the upper bound (as Erschler–Zheng cite it, p. 2) — the first Grigorchuk group has v_{G,S}(n) ⩽ exp(Cn^{α_0})
-- statement:
--   Let $G$ be the first Grigorchuk group (`Garrido.GrigorchukGroup`) and $S$ a finite set generating it. There is a constant $C$ such that for every $n \in \mathbb N$ the ball of radius $n$ (`Chou.wordBall`, products of at most $n$ elements of $S \cup S^{-1}$) has at most $\exp(C n^{\alpha_0})$ elements, where $\alpha_0 = \log 2/\log \lambda_0$ (`ErschlerZheng.alpha0`) and $\lambda_0$ is the positive root of $X^3 - X^2 - 2X - 4$.
--
--   Erschler and Zheng, p. 2: “The upper bound in [5, 43] states that $v_{G,S}(n) \leqslant \exp(Cn^{\alpha_0})$, where $\alpha_0 = \frac{\log 2}{\log \lambda_0} \approx 0.7674$, where $\lambda_0$ is the positive root of the polynomial $X^3 - X^2 - 2X - 4$.”
--
--   The statement is for every finite generating set, the form of the published Grigorchuk–Pak growth bounds; the paper's $S = \{a, b, c, d\}$ is one of them.
-- source:
--   Bartholdi, L., The growth of Grigorchuk's torsion group, Internat. Math. Res. Notices 1998, no. 20, 1049–1054, https://doi.org/10.1155/S1073792898000622, p. 2, the upper bound, and Muchnik, R. and Pak, I., On growth of Grigorchuk groups, Internat. J. Algebra Comput. 11 (2001) 1–17, https://doi.org/10.1142/S0218196701000450, as cited in Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 2

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

namespace Bartholdi

theorem card_wordBall_le_exp_mul_rpow_alpha0 (S : Finset Garrido.GrigorchukGroup)
    (hS : Subgroup.closure (S : Set Garrido.GrigorchukGroup) = ⊤) :
    ∃ C : ℝ, ∀ n : ℕ, (Nat.card (Chou.wordBall (S : Set Garrido.GrigorchukGroup) n) : ℝ) ≤
      Real.exp (C * (n : ℝ) ^ ErschlerZheng.alpha0) := by
  sorry

end Bartholdi
