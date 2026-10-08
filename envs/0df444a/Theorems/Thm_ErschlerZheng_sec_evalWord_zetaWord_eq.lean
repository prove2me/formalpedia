-- Prove2me | Theorems.Thm_ErschlerZheng_sec_evalWord_zetaWord_eq
-- name    : ErschlerZheng.sec_evalWord_zetaWord_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T00:48:06.428464+00:00
-- url     : https://prove2.me/theorems/fa8493d5-f8ee-4b66-8fb2-efecb99b3fe6
-- title:
--   (2.3), corrected — ψ_n(ζ_{ω_n}(w)) is (awa, w) when ζ_{ω_n}(w) has an even number of a, and (aw, wa)ε when it has an odd number
-- statement:
--   Let $\omega \in \{\mathbf 0, \mathbf 1, \mathbf 2\}^{\mathbb N}$, $n \in \mathbb N$ and $w$ a word over $\{ab, ac, ad\}$. Let $g$ be the value of the word $\zeta_{\omega_n}(w)$ in $G_{\mathfrak s^n\omega}$ and $h$ the value of $w$ in $G_{\mathfrak s^{n+1}\omega}$ (`evalWord`, `zetaWord`), and let $N$ be the number of letters $a$ in $\zeta_{\omega_n}(w)$. With $g_v$ the section of $g$ at the vertex $v$ for the right action (`sec`):
--
--   - if $N$ is even, $g$ fixes the two vertices of level 1 (`levelStab ⊤ 1`), $g_0 = a h a$ and $g_1 = h$;
--   - if $N$ is odd, $0 \cdot g = 1$, $g_0 = a h$ and $g_1 = h a$.
--
--   That is, $\psi_n(\zeta_{\omega_n}(w)) = (awa, w)$ in the even case and $(aw, wa)\varepsilon$ in the odd case.
--
--   Erschler and Zheng, p. 15: “One step wreath recursion gives that for $w \in \{ab, ac, ad\}^*$, (2.3) $\psi_n(\zeta_{\omega_n}(w)) = (awa, w)$ if $\zeta_{\omega_n}(w)$ contains an even number of $a$, $(wa, aw)\varepsilon$ if $\zeta_{\omega_n}(w)$ contains an odd number of $a$.”
--
--   The odd case is corrected from the printed $(wa, aw)\varepsilon$, which fails ([`ErschlerZheng.not_forall_sec_evalWord_zetaWord_eq_mul_grigA_and_grigA_mul_of_odd`](https://prove2.me/theorems/f95803f1-e432-47fd-9c8f-9fb2ebf25a41)), to $(aw, wa)\varepsilon$; the even case is as printed. The display is a two-line case distinction in the paper.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 15, (2.3), corrected

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk
open scoped RightActions

namespace ErschlerZheng

theorem sec_evalWord_zetaWord_eq (ω : ℕ → Fin 3) (n : ℕ) (w : List APair) :
    (Even (((zetaWord (ω n) w).flatMap APair.toWord).count .a) →
      evalWord ω n ((zetaWord (ω n) w).flatMap APair.toWord) ∈ levelStab ⊤ 1 ∧
        sec (evalWord ω n ((zetaWord (ω n) w).flatMap APair.toWord)) [false] =
          Garrido.grigA * evalWord ω (n + 1) (w.flatMap APair.toWord) * Garrido.grigA ∧
        sec (evalWord ω n ((zetaWord (ω n) w).flatMap APair.toWord)) [true] =
          evalWord ω (n + 1) (w.flatMap APair.toWord)) ∧
    (Odd (((zetaWord (ω n) w).flatMap APair.toWord).count .a) →
      [false] <• evalWord ω n ((zetaWord (ω n) w).flatMap APair.toWord) = [true] ∧
        sec (evalWord ω n ((zetaWord (ω n) w).flatMap APair.toWord)) [false] =
          Garrido.grigA * evalWord ω (n + 1) (w.flatMap APair.toWord) ∧
        sec (evalWord ω n ((zetaWord (ω n) w).flatMap APair.toWord)) [true] =
          evalWord ω (n + 1) (w.flatMap APair.toWord) * Garrido.grigA) := by
  sorry

end ErschlerZheng
