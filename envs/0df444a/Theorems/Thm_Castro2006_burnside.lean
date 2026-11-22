-- Prove2me | Theorems.Thm_Castro2006_burnside
-- name    : Castro2006.burnside
-- status  : Proved
-- author  : @LG
-- created : 2026-11-18T20:42:43.201373+00:00
-- url     : https://prove2.me/theorems/83440b49-b0f9-41a7-8f53-e2ad3555a0c1
-- title:
--   Burnside: $p$-group with a unique subgroup of order $p$ (Teorema 4.5.2)
-- statement:
--   If $G$ is a $p$-group containing a unique subgroup of order $p$, then $G$ is cyclic or a generalized quaternion group.
-- source:
--   https://web.archive.org/web/20070509023602/http://www.mat.ibilce.unesp.br/posgraduacao/dissertacoes/dissertacao_Francielle.pdf

import Mathlib

namespace Castro2006
theorem burnside {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Fintype G]
    (hG : IsPGroup p G) (hunique : ∃! H : Subgroup G, Nat.card H = p) :
    IsCyclic G ∨ ∃ m : ℕ, 1 ≤ m ∧ Nonempty (G ≃* QuaternionGroup (2 ^ m)) := by sorry
end Castro2006
