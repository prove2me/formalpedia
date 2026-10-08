-- Prove2me | Theorems.Thm_ErschlerZheng_not_forall_sec_evalWord_zetaWord_eq_mul_grigA_and_grigA_mul_of_odd
-- name    : ErschlerZheng.not_forall_sec_evalWord_zetaWord_eq_mul_grigA_and_grigA_mul_of_odd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:15:29.540475+00:00
-- url     : https://prove2.me/theorems/f95803f1-e432-47fd-9c8f-9fb2ebf25a41
-- title:
--   (2.3), as printed, fails — the odd case ψ_n(ζ_{ω_n}(w)) = (wa, aw)ε does not hold for ω = (012)^∞, n = 0, w = ad
-- statement:
--   It is not true that for every $\omega \in \{\mathbf 0, \mathbf 1, \mathbf 2\}^{\mathbb N}$, every $n \in \mathbb N$ and every word $w$ over $\{ab, ac, ad\}$ such that $\zeta_{\omega_n}(w)$ contains an odd number of letters $a$, the value $g$ of $\zeta_{\omega_n}(w)$ in $G_{\mathfrak s^n\omega}$ and the value $h$ of $w$ in $G_{\mathfrak s^{n+1}\omega}$ (`evalWord`, `zetaWord`) satisfy $g_0 = h a$ and $g_1 = a h$, where $g_v$ is the section of $g$ at the vertex $v$ for the right action (`sec`) and $a$ is `Garrido.grigA`. These two equations are the sections of the printed odd case $(wa, aw)\varepsilon$.
--
--   Erschler and Zheng, p. 15: “One step wreath recursion gives that for $w \in \{ab, ac, ad\}^*$, (2.3) $\psi_n(\zeta_{\omega_n}(w)) = (awa, w)$ if $\zeta_{\omega_n}(w)$ contains an even number of $a$, $(wa, aw)\varepsilon$ if $\zeta_{\omega_n}(w)$ contains an odd number of $a$.”
--
--   This is not a result of the paper. It is the negation of the sections of the odd case of (2.3) as printed; the swap $\varepsilon$ is not part of the negated claim. It backs the *Correction* of the note `sec_evalWord_zetaWord_eq`, which corrects the odd case from the printed $(wa, aw)\varepsilon$ to $(aw, wa)\varepsilon$; the corrected form is the milestone `ErschlerZheng.sec_evalWord_zetaWord_eq`.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 15, (2.3), the odd case as printed (fails)

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

namespace ErschlerZheng

theorem not_forall_sec_evalWord_zetaWord_eq_mul_grigA_and_grigA_mul_of_odd :
    ¬ ∀ (ω : ℕ → Fin 3) (n : ℕ) (w : List APair),
      Odd (((zetaWord (ω n) w).flatMap APair.toWord).count .a) →
        sec (evalWord ω n ((zetaWord (ω n) w).flatMap APair.toWord)) [false] =
            evalWord ω (n + 1) (w.flatMap APair.toWord) * Garrido.grigA ∧
          sec (evalWord ω n ((zetaWord (ω n) w).flatMap APair.toWord)) [true] =
            Garrido.grigA * evalWord ω (n + 1) (w.flatMap APair.toWord) := by
  sorry

end ErschlerZheng
