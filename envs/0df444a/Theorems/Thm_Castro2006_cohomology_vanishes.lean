-- Prove2me | Theorems.Thm_Castro2006_cohomology_vanishes
-- name    : Castro2006.cohomology_vanishes
-- status  : Proved
-- author  : @LG
-- created : 2026-11-18T20:25:38.296687+00:00
-- url     : https://prove2.me/theorems/429bed55-78b1-4515-b8f6-6fa5ff1c531b
-- title:
--   Coprime vanishing of $H^n(G,A)$ (Proposição 4.4.1(ii))
-- statement:
--   If $G$ is finite, $A$ is a finite $\mathbb{Z}G$-module, and $\gcd(|G|,|A|)=1$, then $H^n(G,A)=0$ for every $n\ge1$.
-- source:
--   https://web.archive.org/web/20070509023602/http://www.mat.ibilce.unesp.br/posgraduacao/dissertacoes/dissertacao_Francielle.pdf

import Mathlib
open CategoryTheory

namespace Castro2006
theorem cohomology_vanishes {G : Type} [Group G] [Fintype G] (A : Rep ℤ G) [Fintype A] (n : ℕ)
    (hn : 1 ≤ n) (hcop : (Fintype.card G).Coprime (Fintype.card A)) :
    ∀ x : groupCohomology A n, x = 0 := by sorry
end Castro2006
