-- Prove2me | Theorems.Thm_BipColorHard_proposition_9
-- name    : BipColorHard.proposition_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:05.053779+00:00
-- url     : https://prove2.me/theorems/83d34723-b5b2-4d39-b684-2f05abe1372e
-- title:
--   Proposition 9 — bipartite phase labeling reduces to $q$-coloring at degree $D$
-- statement:
--   Let $q=2k+1\ge3$ with $D$ as above. There is a fixed $u\in(0,1/k)$ such that, for every fixed integer $D_0\ge1$ and every fixed $\eta>0$, there is a constant $c>0$ such that the following holds. A polynomial-time algorithm that approximates $Z_q(G)$ within a factor $e^{c|V(G)|}$ on simple bipartite graphs $G$ of maximum degree at most $D$ yields a polynomial-time algorithm that approximates $Z_{W_u}(H)$ within a factor $e^{\eta|V(H)|}$ on bipartite multigraphs $H$ of maximum degree at most $D_0$.
--
--   Precisely, there are a polynomial-time map $H\mapsto G_H$ and a polynomial-time answer map such that, on $H$ of maximum degree at most $D_0$, $G_H$ is bipartite of maximum degree at most $D$, and every rational within $e^{\pm c|V(G_H)|}$ of $Z_q(G_H)$ is turned into a rational within $e^{\pm\eta|V(H)|}$ of $Z_{W_u}(H)$.
--
--   This is the second reduction of the proof of Theorem 1. The fixed $u$ comes from the gadget.
--
--   Differences from the source:
--   - reading: "a polynomial-time algorithm ... yields a polynomial-time algorithm" → one query to the approximation, post-processed, correct for every admissible rational answer; reason: §6.1 builds exactly this reduction
--   - encoding: bipartite multigraphs $H$ → `PhaseInst` with unary sizes and a list of edges, encoded by `encPhase`; reason: with binary sizes the output of the map could be exponentially long
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), Proposition 9, p.7 (PDF p.9)

import Definitions.Def_BipColorHard_Hardness
import Definitions.Def_BipColorHard_PhaseLabeling

set_option autoImplicit false

namespace BipColorHard

open NSWApxHard.Reduction (GraphInput encGraph) in
/-- **Proposition 9**, p.7 (PDF p.9), manuscript sha256 78a66d1f…, for `q = 2k + 1 ≥ 3`, `D` of §3. There is a fixed `u ∈ (0, 1/k)` such that,
for every fixed integer `D₀ ≥ 1` and every fixed `η > 0`, there is a constant `c > 0` such that the following holds. A polynomial-time
algorithm that approximates `Z_q(G)` within a factor `e^{c|V(G)|}` on simple bipartite graphs `G` of maximum degree at most `D` yields a
polynomial-time algorithm that approximates `Z_{W_u}(H)` within a factor `e^{η|V(H)|}` on bipartite multigraphs `H` of maximum degree at
most `D₀`.

**Formalization Note.** "Yields" is a reduction with one query, as in the proof (§6.1): an instance map `f`, computed on encodings by the
polynomial-time `fs`, and a polynomial-time answer map `ans`, correct for every admissible rational answer. -/
theorem proposition_9 (k : ℕ) (hk : 1 ≤ k) :
    ∃ u : ℝ, 0 < u ∧ u < 1 / (k : ℝ) ∧ ∀ D0 : ℕ, 1 ≤ D0 → ∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 < c ∧
      ∃ (f : PhaseInst → GraphInput) (fs : List Bool → List Bool)
        (ans : List (Option (Bool ⊕ Bool)) → List Bool),
        CookPvsNP.PolyTimeComputable fs ∧ CookPvsNP.PolyTimeComputable ans ∧
        ∀ H : PhaseInst, H.DegLe D0 →
          fs (encPhase H) = encGraph (f H) ∧
          (f H).G.IsBipartite ∧ MaxDegLe (bipDeg (2 * k + 1)) (f H) ∧
          ∀ r : ℚ, WithinExp (c * ((f H).N : ℝ)) (coloringCount (2 * k + 1) (f H) : ℝ) r →
            ∃ r' : ℚ, ans (IIDMatchHard.pairInput (encPhase H) r) = ImpatientMatching.encRat r' ∧
              WithinExp (η * ((H.nL : ℝ) + (H.nR : ℝ))) (phaseZ k u H) r' := by sorry

end BipColorHard
