-- Prove2me | Theorems.Thm_Castro2006_lema_4_5_2
-- name    : Castro2006.lema_4_5_2
-- status  : Proved
-- author  : @LG
-- created : 2026-11-18T20:25:00.457074+00:00
-- url     : https://prove2.me/theorems/48b98135-db59-4129-8d2a-0eee0bacd1c3
-- title:
--   Congruence for units of order $p$ modulo $p^n$ (Lema 4.5.2)
-- statement:
--   Let $p$ be prime, $a$ an integer, $n\ge2$, with $a^p\equiv1\pmod{p^n}$ but $a\not\equiv1\pmod{p^n}$. If $p$ is odd then $a\equiv1\pmod{p^{n-1}}$; if $p=2$ then $a\equiv\pm1\pmod{2^{n-1}}$.
-- source:
--   https://web.archive.org/web/20070509023602/http://www.mat.ibilce.unesp.br/posgraduacao/dissertacoes/dissertacao_Francielle.pdf

import Mathlib

namespace Castro2006
theorem lema_4_5_2 {p : ℕ} (hp : p.Prime) (a : ℤ) (n : ℕ) (hn : 2 ≤ n)
    (hap : a ^ p ≡ 1 [ZMOD p ^ n]) (ha1 : ¬(a ≡ 1 [ZMOD p ^ n])) :
    (p ≠ 2 → a ≡ 1 [ZMOD p ^ (n - 1)]) ∧
    (p = 2 → (a ≡ 1 [ZMOD 2 ^ (n - 1)] ∨ a ≡ -1 [ZMOD 2 ^ (n - 1)])) := by sorry
end Castro2006
