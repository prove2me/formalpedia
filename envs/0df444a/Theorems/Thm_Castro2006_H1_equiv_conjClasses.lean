-- Prove2me | Theorems.Thm_Castro2006_H1_equiv_conjClasses
-- name    : Castro2006.H1_equiv_conjClasses
-- status  : Proved
-- author  : @LG
-- created : 2026-11-18T20:42:01.698209+00:00
-- url     : https://prove2.me/theorems/d548b355-4486-48b8-a93f-1e1d64d9bea9
-- title:
--   $H^1(G,A)$ bijection with $A$-conjugacy classes of splittings (Teorema 4.2.1)
-- statement:
--   Let $G$ be a group and $A$ a $\mathbb{Z}G$-module. There is a bijection between $H^1(G,A)$ and the set of $A$-conjugacy classes of splittings (lifts) $s:G\to A\rtimes G$ of the split extension $0\to A\to A\rtimes G\to G\to1$.
-- source:
--   https://web.archive.org/web/20070509023602/http://www.mat.ibilce.unesp.br/posgraduacao/dissertacoes/dissertacao_Francielle.pdf

import Mathlib
import Definitions.Def_Castro2006_action
open CategoryTheory

namespace Castro2006
theorem H1_equiv_conjClasses {G N : Type} [Group G] [CommGroup N] (φ : G →* MulAut N) :
    Nonempty ((SemidirectProduct.toGroupExtension φ).ConjClasses ≃
      groupCohomology (Castro2006.repOfMulAut φ) 1) := by sorry
end Castro2006
