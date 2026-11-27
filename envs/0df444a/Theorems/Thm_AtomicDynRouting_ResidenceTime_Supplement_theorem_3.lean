-- Prove2me | Theorems.Thm_AtomicDynRouting_ResidenceTime_Supplement_theorem_3
-- name    : AtomicDynRouting.ResidenceTime.Supplement.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T06:34:45.718805+00:00
-- url     : https://prove2.me/theorems/e4a973cc-5983-4fa2-b88b-4d6747017e42
-- title:
--   Theorem 3, p. 14 — at equilibrium of Γ1, Γ2 (UFR) or Γ3 (NE): global FIFO, and earlier batches are neither overtaken nor influenced by later ones
-- statement:
--   Consider any of the ADR games $\Gamma_1$, $\Gamma_2$ or $\Gamma_3$ on a finite acyclic unit-capacity network $G$ with a single OD pair $(o,d)$ and finitely many agents entering at each integer time. Let $p$ be a UFR equilibrium if the game is $\Gamma_1$ or $\Gamma_2$, and a Nash equilibrium if the game is $\Gamma_3$. Then:
--
--   1. **Global FIFO.** If under $p$ agent $i$ preempts agent $j$ at some vertex $v$ (including the origin $o$), then
--   $$t^d_i(p)\le t^d_j(p).$$
--   2. **No overtaking.** Let $F=\{i: t^d_i(p)\le T\}$ be the agents of a batch together with all earlier batches. For every path profile $q$ in which the agents of $F$ follow their routes in $p$ and the other agents choose arbitrary $o$-$d$ paths, every agent of $F$ preempts every agent outside $F$ at every common vertex of their routes; therefore the arrival time of every agent of $F$ at every vertex is the same under $q$ as under $p$.
--
--   For $\Gamma_1$ and $\Gamma_2$ the theorem follows from Lemma 8; for $\Gamma_3$ part 1 is Theorem EC.6 and part 2 a consequence of Theorem 2 in Cao, Chen, Chen, Wang (Atomic dynamic flow games: adaptive vs. nonadaptive agents). The theorem shows that the hypothesis of Theorem 1 holds at equilibrium.
--
--   Differences from the source:
--
--   - encoding: the three games of §5.1 with their priority lists → Game with Rule r1/r2/r3; priorities as strict total orders (Γ3: an order of all of E per vertex, one global original order) and the run built by recursion on time; reason: only the restrictions to incoming edges and to each Δ_r are used, and every family of such orders is a restriction; the recursion is the deterministic dynamics the rules determine
--   - encoding: arrival times t^v_j(p), ∞ off the route → ℕ∞-valued arrTime (⊤ off the route); reason: Lean convention; same values
--   - reading: 'agents of a batch and those in all earlier batches' → F = {i | t^d_i(p) ≤ T} for every T ∈ ℕ; reason: for T a batch time this is exactly that set; for any other T it is the set of the largest batch time ≤ T, or empty, so the quantification covers exactly the source's sets
--   - reading: 'cannot be influenced by the latter agents' → t^v_i(q) = t^v_i(p) for every agent i ∈ F and every vertex v; reason: the latter agents' choices are the only difference between q and p
-- source:
--   Cao, Chen, Chen, Wang, Bounding residence times for atomic dynamic routings, accepted manuscript (Mathematics of Operations Research, accepted Nov. 12, 2021; WRAP 160244), p. 14 (PDF 15), Theorem 3 (games: pp. 12–13, PDF 13–14; Definitions 4–6)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Supplement_Equilibrium

namespace AtomicDynRouting.ResidenceTime.Supplement

open AtomicDynRouting.ResidenceTime

theorem theorem_3 {ι V E : Type} [Fintype V] [Fintype E] (G : Game ι V E) (hN : G.N.Acyclic) (hG : G.Standing) (p : ι → List E) (hp : G.IsEquilibrium p) :
    (∀ i j v, G.preempts p i j v → G.arrTime p i G.d ≤ G.arrTime p j G.d) ∧
    (∀ (T : ℕ) (q : ι → List E), G.IsProfile q → (∀ i ∈ G.batchesUpTo p T, q i = p i) →
      (∀ i ∈ G.batchesUpTo p T, ∀ j ∉ G.batchesUpTo p T, ∀ v,
          G.passes q i v → G.passes q j v → G.preempts q i j v) ∧
      (∀ i ∈ G.batchesUpTo p T, ∀ v, G.arrTime q i v = G.arrTime p i v)) := by sorry

end AtomicDynRouting.ResidenceTime.Supplement
