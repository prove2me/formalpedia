-- Prove2me | Theorems.Thm_EntropyLocalCoord_Leader_Supplement_theorem_3_4
-- name    : EntropyLocalCoord.Leader.Supplement.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:28:27.534025+00:00
-- url     : https://prove2.me/theorems/d8ae50ac-921f-4442-9a88-94a21dfbcdcc
-- title:
--   Theorem 3.4 — graphs with $I_{\mathrm{leader}}(G,r)\ge C\,I_{\mathrm{bin}}(G,r)\sqrt{\log_2(1/I_{\mathrm{bin}}(G,r))}$ for every radius
-- statement:
--   For a finite simple graph $G$ and an integer $r\ge1$ let $I_{\mathrm{bin}}(G,r)$ and $I_{\mathrm{leader}}(G,r)$ be the binary and leader inefficiencies of $G$ for the radius-$r$ information skeleton $\mathfrak S(G,r)$, in which each player observes the vertices at graph distance at most $r$.
--
--   There are universal constants $c,A,C>0$ with the following property. For every integer $r\ge1$ there is a threshold $k_0(r)$ such that for every integer $k\ge k_0(r)$ there exists a finite simple graph $G$ satisfying simultaneously
--
--   $$I_{\mathrm{leader}}(G,r)\ \ge\ c\,\sqrt k\,2^{-k},\qquad I_{\mathrm{bin}}(G,r)\ \le\ A\,2^{-k},$$
--
--   and
--
--   $$I_{\mathrm{leader}}(G,r)\ \ge\ C\,I_{\mathrm{bin}}(G,r)\sqrt{\log_2\bigl(1/I_{\mathrm{bin}}(G,r)\bigr)}.$$
--
--   Only $k_0$ depends on $r$; $c$, $A$ and $C$ depend on neither $k$ nor $r$. The theorem shows that the conjectured universal linear bound $I_{\mathrm{leader}}\le C'\,I_{\mathrm{bin}}$ fails, and that the logarithmic loss in the mission's goal (Theorem 3.2) cannot be removed beyond a square root.
--
--   Differences from the source:
--   - encoding: Ileader(G,r) = Ω(√k 2^{−k}) and Ibin(G,r) = O(2^{−k}) with implicit constants independent of k and r → ∃ c A > 0, quantified before r, with c·√k·2^{−k} ≤ Ileader(G,r) and Ibin(G,r) ≤ A·2^{−k}; reason: the one-sided Ω and O bounds with universal constants, as the pitfall list of the brief spells out
--   - encoding: a finite graph G → a simple graph on Fin n for some n; reason: every finite simple graph is isomorphic to one on Fin n, and Ileader, Ibin are invariant under relabelling
--   - encoding: dist_G(i,j) ≤ r in B_r(i) → SimpleGraph.edist i j ≤ r in ℕ∞ (⊤ for disconnected vertices); reason: the shortest-path distance with disconnected vertices at infinity
--   - encoding: C·Ibin·√(log₂(1/Ibin)), defined for Ibin > 0 → the same expression with Lean's 1/0 = 0, log 0 = 0 and √ of a negative = 0; reason: the source's expression is undefined at Ibin = 0; for the graphs of the theorem Ibin > 0 follows from Ileader > 0 and Theorem 3.2, and Ibin ≤ A·2^{−k} < 1 for large k, so no instance changes
-- source:
--   Peretz and Kraizberg, Entropy Bounds for Local Coordination and Graph Amenability, STOC 2027 submission #272 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/272.pdf, SHA-256 ed0fb53954295c5258fc56b2780b62aad05401917ee1fb4064ff953d9d1d0526, Theorem 3.4, p. 8; proof §5, pp. 13–20 (r = 1, pp. 13–19; extension to arbitrary r, pp. 19–20); S(G, r), §2, p. 6.

import Mathlib
import Definitions.Def_EntropyLocalCoord_Leader_Model
import Definitions.Def_EntropyLocalCoord_Leader_Supplement_Radius

namespace EntropyLocalCoord.Leader.Supplement

/-- Peretz--Kraizberg, STOC 2027 submission #272, Theorem 3.4, p. 8 (proof §5, pp. 13--20).
There are universal constants `c, A, C > 0` such that for every integer radius `r ≥ 1` there is
a threshold `k₀` (depending on `r`) such that for every integer `k ≥ k₀` some finite simple graph
`G` satisfies, simultaneously, `I_leader(G, r) ≥ c √k 2^{-k}`, `I_bin(G, r) ≤ A 2^{-k}` and
`I_leader(G, r) ≥ C I_bin(G, r) √(log₂ (1 / I_bin(G, r)))`. -/
theorem theorem_3_4 :
    ∃ c A C : ℝ, 0 < c ∧ 0 < A ∧ 0 < C ∧
      ∀ r : ℕ, 1 ≤ r → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
        ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
          c * (Real.sqrt k * (2 : ℝ) ^ (-(k : ℤ))) ≤ IleaderR G r ∧
          IbinR G r ≤ A * (2 : ℝ) ^ (-(k : ℤ)) ∧
          C * IbinR G r * Real.sqrt (Real.logb 2 (1 / IbinR G r)) ≤ IleaderR G r := by sorry

end EntropyLocalCoord.Leader.Supplement
