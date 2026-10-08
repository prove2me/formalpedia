-- Prove2me | Theorems.Thm_ErschlerZheng_iota_comm_mem_rist_and_wordLength_le
-- name    : ErschlerZheng.iota_comm_mem_rist_and_wordLength_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T03:54:27.916085+00:00
-- url     : https://prove2.me/theorems/a79d5b15-30f0-4e12-9354-8d30ad7d705f
-- title:
--   Fact 7.6 — if ω_{n−1}(γ) = id, then for every v ∈ L_n the element ι([γ_{𝔰^nω}, a], v) lies in Rist_{G_ω}(v) and has word length ⩽ 2^{n+2}
-- statement:
--   Let $\omega$ satisfy Assumption $(\mathrm{Fr}(D))$ (`SatisfiesFr`), let $n \ge 1$, and let $\gamma \in \{b, c, d\}$ (`BCD`) be a letter with $\omega_{n-1}(\gamma) = id$ (`letterValue (ω (n - 1)) γ = false`). Then for every vertex $v$ of length $n$, the element $\iota([\gamma_{\mathfrak s^n\omega}, a], v)$ (`iota`), which acts as $[\gamma_{\mathfrak s^n\omega}, a]$ on the subtree below $v$ and trivially elsewhere:
--
--   1. lies in the rigid stabilizer of $v$ in $G_\omega$ (`rist (grigorchuk ω) v`), so in particular in $G_\omega$;
--   2. has word length at most $2^{n+2}$ with respect to $\{a, b_\omega, c_\omega, d_\omega\}$ (`wordLength`, `gens`).
--
--   Erschler and Zheng, p. 36: “Fact 7.6. For $n \in \mathbb N$, let $\gamma$ be the letter in $\{b, c, d\}$ be such that $\omega_{n-1}(\gamma) = id$. Then for any vertex $v \in \mathsf L_n$, $[\gamma_{\mathfrak s^n\omega}, a]$ is in the rigid stabilizer $\mathrm{Rist}_{G_\omega}(v)$ and $|\iota([\gamma_{\mathfrak s^n\omega}, a], v)| \leqslant 2^{n+2}$.”
--
--   The membership is stated for $\iota([\gamma_{\mathfrak s^n\omega}, a], v)$, the element of Figure 7.2 (“The element $[\gamma_{\mathfrak s^n\omega}, a]$ is in the level $n$ rigid stabilizer. By definition, the element $\iota([\gamma_{\mathfrak s^n\omega}, a], v)$ only has nontrivial section at $v$.”), placed at $v$; $|\cdot|$ is $|\cdot|_{G_\omega}$ (p. 35: “Recall that $|\cdot|_{G_\omega}$ denotes the word length in the group $G_\omega$ equipped with generating set $\{a, b_\omega, c_\omega, d_\omega\}$”). The Lean commutator is $ghg^{-1}h^{-1}$; $\gamma_{\mathfrak s^n\omega}$ and $a$ are involutions (the bundle lemmas `ErschlerZheng.genFun_involutive` and `Garrido.grigAFun_involutive`), so every convention gives $\gamma a \gamma a$. $n \ge 1$ makes $\omega_{n-1}$ a letter of $\omega$. The standing assumption is that of §7.2 (p. 35).
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 36, Fact 7.6

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
open scoped commutatorElement

namespace ErschlerZheng

theorem iota_comm_mem_rist_and_wordLength_le (D : ℕ) (ω : ℕ → Fin 3) (hω : SatisfiesFr D ω)
    (n : ℕ) (hn : 1 ≤ n) (γ : BCD) (hγ : letterValue (ω (n - 1)) γ = false) (v : List Bool)
    (hv : v.length = n) :
    iota ⁅gen (shiftSeq ω n) γ, Garrido.grigA⁆ v ∈ rist (grigorchuk ω) v ∧
      wordLength (gens ω) (iota ⁅gen (shiftSeq ω n) γ, Garrido.grigA⁆ v) ≤ 2 ^ (n + 2) := by
  sorry

end ErschlerZheng
