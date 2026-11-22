-- Prove2me | Theorems.Thm_Castro2006_schur_zassenhaus_abelian
-- name    : Castro2006.schur_zassenhaus_abelian
-- status  : Proved
-- author  : @LG
-- created : 2026-11-18T20:25:56.431585+00:00
-- url     : https://prove2.me/theorems/8d3c9404-a273-4a79-baa7-ef81f8caa93b
-- title:
--   Schur–Zassenhaus, abelian kernel, with conjugacy of complements (Teorema 4.4.1)
-- statement:
--   Let $E$ be a finite group of order $k\cdot m$ with $\gcd(k,m)=1$, and $A$ an abelian normal subgroup of order $k$. Then the extension $0\to A\to E\to E/A\to1$ splits (so $E$ is a semidirect product of $A$ by $E/A$ and contains a subgroup of order $m$), and any two subgroups of $E$ of order $m$ are conjugate.
-- source:
--   https://web.archive.org/web/20070509023602/http://www.mat.ibilce.unesp.br/posgraduacao/dissertacoes/dissertacao_Francielle.pdf

import Mathlib

namespace Castro2006
theorem schur_zassenhaus_abelian {E : Type} [Group E] [Fintype E] (k m : ℕ)
    (hcard : Fintype.card E = k * m) (hcop : k.Coprime m)
    (A : Subgroup E) [A.Normal] [IsMulCommutative A] (hA : Nat.card A = k) :
    (∃ H : Subgroup E, H.IsComplement' A) ∧
    (∀ H₁ H₂ : Subgroup E, Nat.card H₁ = m → Nat.card H₂ = m →
      ∃ g : E, H₁.map (MulAut.conj g).toMonoidHom = H₂) := by sorry
end Castro2006
