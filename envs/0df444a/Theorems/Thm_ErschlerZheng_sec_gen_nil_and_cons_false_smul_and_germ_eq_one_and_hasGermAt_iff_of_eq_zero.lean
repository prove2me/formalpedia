-- Prove2me | Theorems.Thm_ErschlerZheng_sec_gen_nil_and_cons_false_smul_and_germ_eq_one_and_hasGermAt_iff_of_eq_zero
-- name    : ErschlerZheng.sec_gen_nil_and_cons_false_smul_and_germ_eq_one_and_hasGermAt_iff_of_eq_zero
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:15:49.708535+00:00
-- url     : https://prove2.me/theorems/170be4e5-5b6d-4ac3-85f3-c8c29ddb4cea
-- title:
--   Example 3.2, bundle reading — for ω_0 = 0, d_ω is its own section at the root, yet fixes every vertex below 0 and has trivial germ at 01^∞; it has a d-germ there iff ω is eventually 0
-- statement:
--   Let $\omega = \omega_0\omega_1\ldots$ be a string over $\{\mathbf 0, \mathbf 1, \mathbf 2\}$ (`ω : ℕ → Fin 3`) with $\omega_0 = \mathbf 0$, let $d_\omega$ be the generator `gen ω .d` of $G_\omega$, and let $x = 01^\infty$ (`prepend [false] oneRay`). Then: the section of $d_\omega$ at the empty vertex (`sec (gen ω .d) []`) is $d_{\mathfrak s^0\omega}$ (`gen (shiftSeq ω 0) .d`); $d_\omega$ fixes every vertex $0v$ below $0$, that is, $(0v) \cdot d_\omega = 0v$ for every finite word $v$ (`false :: v`); the germ of $d_\omega$ at $x$ (`germ`) is the identity; and $d_\omega$ has a $d$-germ at $x$ in the sense of `HasGermAt` (`HasGermAt ω .d (gen ω .d) (prepend [false] oneRay)`) if and only if $\omega_k = \mathbf 0$ for all large $k$ (`∀ᶠ k in Filter.atTop, ω k = 0`).
--
--   This is not a result of the paper. It backs the sentence of the bundle note `ErschlerZheng_Grigorchuk` on `HasGermAt`: “Without it, the definition would say that $d_\omega$ has a $d$-germ at $x = 01^\infty$ when $\omega_0 = \mathbf 0$ (its section at the empty prefix is $d_\omega$ itself), although $d_\omega$ then fixes every vertex below $0$ and its germ at $x$ is trivial.” The first three parts are the three facts of that sentence; the first is the printed condition, without $x = x_1 \ldots x_n 1^\infty$, met at the level $n = 0$. The last part says what the bundle's definition, with that condition, gives at $x$: a $d$-germ only when all but finitely many letters of $\omega$ are $\mathbf 0$.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 18, the γ-germs of Example 3.2 at x = x_1…x_n1^∞ (supporting fact, not in the paper)

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

open scoped RightActions

namespace ErschlerZheng

theorem sec_gen_nil_and_cons_false_smul_and_germ_eq_one_and_hasGermAt_iff_of_eq_zero
    (ω : ℕ → Fin 3) (hω : ω 0 = 0) :
    sec (gen ω .d) [] = gen (shiftSeq ω 0) .d ∧
      (∀ v : List Bool, (false :: v) <• gen ω .d = false :: v) ∧
      germ (prepend [false] oneRay) (gen ω .d) = 1 ∧
      (HasGermAt ω .d (gen ω .d) (prepend [false] oneRay) ↔
        ∀ᶠ k in Filter.atTop, ω k = 0) := by
  sorry

end ErschlerZheng
