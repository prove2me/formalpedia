-- Prove2me | Theorems.Thm_ErschlerZheng_sec_mem_grigorchuk_and_schreierDist_smul_le_of_isCofinal
-- name    : ErschlerZheng.sec_mem_grigorchuk_and_schreierDist_smul_le_of_isCofinal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T01:36:12.753375+00:00
-- url     : https://prove2.me/theorems/60144590-2c13-4d70-91ac-45ea18ab4ce5
-- title:
--   Lemma 7.5 — for g ∈ G_ω, g_{x_1…x_n} ∈ G_{𝔰^nω} and d_𝒮(x, x·g) ⩽ 2^n(|g_{x_1…x_n}|_{G_{𝔰^nω}} + 1)
-- statement:
--   For every string $\omega \in \{\mathbf 0, \mathbf 1, \mathbf 2\}^{\mathbb N}$, every $g \in G_\omega$, every $n \in \mathbb N$ and every ray $x$ cofinal with $1^\infty$ (`IsCofinal`), let $g_{x_1 \ldots x_n}$ be the section of $g$ at the vertex $x_1 \ldots x_n$ (`sec g (rayPrefix x n)`). Then
--
--   1. $g_{x_1 \ldots x_n} \in G_{\mathfrak s^n\omega}$;
--   2. $d_{\mathcal S_\omega}(x, x \cdot g) \le 2^n\bigl(|g_{x_1 \ldots x_n}|_{G_{\mathfrak s^n\omega}} + 1\bigr)$,
--
--   where $d_{\mathcal S_\omega}$ is the Schreier distance (`schreierDist`) and $|\cdot|_{G_{\mathfrak s^n\omega}}$ the word length with respect to $\{a, b_{\mathfrak s^n\omega}, c_{\mathfrak s^n\omega}, d_{\mathfrak s^n\omega}\}$ (`wordLength (gens (shiftSeq ω n))`).
--
--   Erschler and Zheng, p. 35: “Recall that $|\cdot|_{G_\omega}$ denotes the word length in the group $G_\omega$ equipped with generating set $\{a, b_\omega, c_\omega, d_\omega\}$.” and Lemma 7.5: “Let $g \in G_\omega$ and $g = (g_v)_{v \in \mathsf L_n}\tau$ be its wreath recursion to level $n$. Then for $x = x_1x_2 \ldots \in \partial \mathsf T$, $d_{\mathcal S}(x, x \cdot g) \leqslant 2^n\left(|g_{x_1 \ldots x_n}|_{G_{\mathfrak s^n\omega}} + 1\right)$.”
--
--   The ray $x$ is taken cofinal with $1^\infty$, since $d_{\mathcal S}$ is the distance in the Schreier graph of $1^\infty$, whose vertices are those rays ([`ErschlerZheng.isLocallyFinite_finitary_and_rightOrbit_eq_and_isAuxiliary`](https://prove2.me/theorems/35c025c8-ffd2-423b-9cf0-001847793406)). The first conjunct is what the printed $|g_{x_1 \ldots x_n}|_{G_{\mathfrak s^n\omega}}$ presupposes; given it, the word length, computed among all tree automorphisms, is the word length in $G_{\mathfrak s^n\omega}$.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 35, Lemma 7.5

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
open scoped RightActions

namespace ErschlerZheng

theorem sec_mem_grigorchuk_and_schreierDist_smul_le_of_isCofinal (ω : ℕ → Fin 3)
    (g : Garrido.BinaryTreeAut) (hg : g ∈ grigorchuk ω) (n : ℕ) (x : Ray) (hx : IsCofinal x) :
    sec g (rayPrefix x n) ∈ grigorchuk (shiftSeq ω n) ∧
      schreierDist ω x (x <• g) ≤
        2 ^ n * (wordLength (gens (shiftSeq ω n)) (sec g (rayPrefix x n)) + 1) := by
  sorry

end ErschlerZheng
