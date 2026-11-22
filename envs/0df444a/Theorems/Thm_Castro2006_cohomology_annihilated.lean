-- Prove2me | Theorems.Thm_Castro2006_cohomology_annihilated
-- name    : Castro2006.cohomology_annihilated
-- status  : Proved
-- author  : @LG
-- created : 2026-11-18T20:25:24.859195+00:00
-- url     : https://prove2.me/theorems/97c96a19-40ce-495c-a5cb-c74346f77a5b
-- title:
--   $|G|$ annihilates $H^n(G,A)$ for $n\ge1$ (Proposição 4.4.1(i))
-- statement:
--   If $G$ is a finite group of order $m$ and $A$ a $\mathbb{Z}G$-module, then $m\cdot H^n(G,A)=0$ for every $n\ge1$; i.e. $m\cdot x=0$ for every $x\in H^n(G,A)$.
-- source:
--   https://web.archive.org/web/20070509023602/http://www.mat.ibilce.unesp.br/posgraduacao/dissertacoes/dissertacao_Francielle.pdf

import Mathlib
open CategoryTheory

namespace Castro2006
theorem cohomology_annihilated {G : Type} [Group G] [Fintype G] (A : Rep ℤ G) (n : ℕ) (hn : 1 ≤ n) :
    ∀ x : groupCohomology A n, (Fintype.card G : ℤ) • x = 0 := by sorry
end Castro2006
