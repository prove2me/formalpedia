-- Prove2me | Theorems.Thm_Castro2006_groups_order_pq
-- name    : Castro2006.groups_order_pq
-- status  : Proved
-- author  : @LG
-- created : 2026-11-18T20:26:23.666776+00:00
-- url     : https://prove2.me/theorems/1dbb6686-4817-411a-b514-10071096e6fc
-- title:
--   Classification of groups of order $pq$ (Corolário 4.4.1)
-- statement:
--   Let $G$ have order $pq$ for distinct primes $p>q$. Then $G$ is cyclic ($G\cong\mathbb{Z}_{pq}$), or $G\cong\mathbb{Z}_p\rtimes\mathbb{Z}_q$ with a nontrivial action (a presentation $\langle\alpha,\beta\mid\alpha^p=\beta^q=1,\ \beta\alpha\beta^{-1}=\alpha^s\rangle$ with $s\not\equiv1\pmod p$, $s^q\equiv1\pmod p$); the latter occurs only if $q\mid p-1$.
-- source:
--   https://web.archive.org/web/20070509023602/http://www.mat.ibilce.unesp.br/posgraduacao/dissertacoes/dissertacao_Francielle.pdf

import Mathlib

namespace Castro2006
theorem groups_order_pq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q < p)
    {G : Type} [Group G] [Fintype G] (hcard : Fintype.card G = p * q) :
    IsCyclic G ∨ (q ∣ p - 1 ∧
      ∃ φ : Multiplicative (ZMod q) →* MulAut (Multiplicative (ZMod p)),
        φ ≠ 1 ∧ Nonempty (G ≃* SemidirectProduct (Multiplicative (ZMod p)) (Multiplicative (ZMod q)) φ)) := by sorry
end Castro2006
