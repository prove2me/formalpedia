-- Prove2me | Theorems.Thm_BanditAlgorithm_partial_monitoring_outside_neighbourhood_strict_gap
-- name    : BanditAlgorithm.partial_monitoring_outside_neighbourhood_strict_gap
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-05T17:24:42.895855+00:00
-- url     : https://prove2.me/theorems/65985c2c-d627-4220-ae31-d4b3716e6990
-- title:
--   Actions outside an edge neighbourhood have a strict loss gap on the edge
-- statement:
--   Let $a,b$ be actions and let $c$ lie outside their neighbourhood $N_{ab}$. Then there is an outcome distribution $u\in C_a\cap C_b$ at which $c$ has strictly larger expected loss than both $a$ and $b$:
--
--   $$
--   \langle\ell_c-\ell_a,u\rangle>0,
--   \qquad
--   \langle\ell_c-\ell_b,u\rangle>0.
--   $$
--
--   This is the pointwise strict-gap fact behind the positive constant $\varepsilon$ in Eq. (37.5). It separates information-gathering actions outside $N_{ab}$ from the actions incident to the edge.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), Theorem 37.12, Step 1, printed pp. 488–489, Eq. (37.5).

import Definitions.Def_PartialMonitoringGame
import Mathlib.Tactic

theorem BanditAlgorithm.partial_monitoring_outside_neighbourhood_strict_gap
    {k d : ℕ} {𝕊 : Type*} (G : PartialMonitoringGame k d 𝕊)
    (a b c : Fin k) (hc : c ∉ pmNeighbourhood G a b) :
    ∃ u ∈ pmCell G a ∩ pmCell G b,
      0 < ∑ i, (G.L c i - G.L a i) * u i ∧
      0 < ∑ i, (G.L c i - G.L b i) * u i := by sorry
