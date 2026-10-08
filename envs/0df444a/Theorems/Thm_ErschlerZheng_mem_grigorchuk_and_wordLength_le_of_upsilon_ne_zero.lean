-- Prove2me | Theorems.Thm_ErschlerZheng_mem_grigorchuk_and_wordLength_le_of_upsilon_ne_zero
-- name    : ErschlerZheng.mem_grigorchuk_and_wordLength_le_of_upsilon_ne_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T09:25:28.581953+00:00
-- url     : https://prove2.me/theorems/0afb2e9b-b3e4-46d2-9a8c-45c9543e97a7
-- title:
--   Lemma 8.1 — every g in the support of υ_n lies in G_ω and has |g| ⩽ 2^{2k_n+2D+4} L^ω_n
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $(k_n)$ satisfy the standing assumption of p. 40 (`IsAdmissibleSeq`), and let $D$ divide $n$. If $\upsilon_n(g) \neq 0$ (`upsilon`), then $g$ lies in $G_\omega$ (`grigorchuk ω`) and its word length with respect to $\{a, b_\omega, c_\omega, d_\omega\}$ (`wordLength (gens ω)`) is at most $2^{2k_n+2D+4}L^\omega_n$, where $L^\omega_n$ is the number (8.1) (`lengthL`).
--
--   Erschler and Zheng, p. 57, Lemma 8.1: “Let $\upsilon_n$ be defined as in (7.10) and $L^\omega_n$ be as in (8.1). Then $\sup\{|g| : g \in \mathrm{supp}\,\upsilon_n\} \leqslant 2^{2k_n+2D+4}L^\omega_n$.” and (8.1): “Define the number $L^\omega_n$ to be (8.1) $L^\omega_n := (1\ 1\ 1)M_{\omega_0} \ldots M_{\omega_{n-1}}(1\ 1\ 1)^T$.”
--
--   The supremum is written as a bound for every element of the support. The first conclusion, that the support lies in $G_\omega$, is what makes $|g|$, the word length in $G_\omega$, meaningful; (7.10) calls $\upsilon_n$ a measure on $G_\omega$. The standing assumptions are those of §7.2 (pp. 35 and 40).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 57, Lemma 8.1

import Mathlib
import Definitions.Def_ErschlerZheng_Construction

namespace ErschlerZheng

theorem mem_grigorchuk_and_wordLength_le_of_upsilon_ne_zero (D : ℕ) (ω : ℕ → Fin 3)
    (hω : SatisfiesFr D ω) (k : ℕ → ℕ) (hk : IsAdmissibleSeq D k) (n : ℕ) (hn : D ∣ n)
    (g : Garrido.BinaryTreeAut) (hg : upsilon D ω k n g ≠ 0) :
    g ∈ grigorchuk ω ∧ wordLength (gens ω) g ≤ 2 ^ (2 * k n + 2 * D + 4) * lengthL ω n := by
  sorry

end ErschlerZheng
