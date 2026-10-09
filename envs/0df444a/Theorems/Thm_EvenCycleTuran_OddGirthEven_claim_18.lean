-- Prove2me | Theorems.Thm_EvenCycleTuran_OddGirthEven_claim_18
-- name    : EvenCycleTuran.OddGirthEven.claim_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:17.367622+00:00
-- url     : https://prove2.me/theorems/86082911-8b20-48e8-be5f-6d68155d5d01
-- title:
--   Claim 18 — uniform edge bounds inside and between distance layers
-- statement:
--   Fix integers $k>l\ge2$. There is a constant $c=c(k,l)\ge2$ such that for every finite graph $G$ with no cycles of lengths $3,\ldots,2l$ or $2k$, and every vertex $v$,
--
--   $$|E(G[N_l(v)])|\le c|N_l(v)|,$$
--
--   $$|E_G(N_l(v),N_{l+1}(v))|\le c\bigl(|N_l(v)|+|N_{l+1}(v)|\bigr).$$
--
--   These bounds control the two kinds of edges needed in the deletion argument for Theorem 17.
--
--   **Formalization Note** The constant is chosen before the graph and vertex, so it depends only on $k,l$, as the notation $c(k,l)$ specifies. The graph has all the short-cycle exclusions from the standing setting of §6.2.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 27, Claim 18

import Mathlib
import Definitions.Def_EvenCycleTuran_OddGirthEven_Setting

namespace EvenCycleTuran.OddGirthEven

/-- Claim 18, p. 27, with one constant depending only on k and l. -/
theorem claim_18 (k l : ℕ) (hl : 2 ≤ l) (hkl : l < k) :
    ∃ c : ℕ, 2 ≤ c ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      EvenCycleTuran.C4Count.CycleFree (Set.Icc 3 (2 * l) ∪ {2 * k}) G →
      ∀ v : Fin n,
        edgesInside G (layer G v l) ≤ c * (layer G v l).ncard ∧
        edgesBetween G (layer G v l) (layer G v (l + 1)) ≤
          c * ((layer G v l).ncard + (layer G v (l + 1)).ncard) := by sorry

end EvenCycleTuran.OddGirthEven
