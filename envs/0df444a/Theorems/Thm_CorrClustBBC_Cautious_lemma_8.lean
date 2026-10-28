-- Prove2me | Theorems.Thm_CorrClustBBC_Cautious_lemma_8
-- name    : CorrClustBBC.Cautious.lemma_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:27.95684+00:00
-- url     : https://prove2.me/theorems/c07eba50-d2d0-4d8c-831d-17461932779d
-- title:
--   Lemma 8, p. 97 — in a δ-clean cluster every vertex w is 3δ-good w.r.t. N⁺(v) of each member v (δ = 1/44)
-- statement:
--   Let $\delta=1/44$. Let $G$ be a complete $\pm$-labelled graph on a finite vertex set $V$, let $R\subseteq V$ be a set of vertices, and let $C\subseteq R$ be $\delta$-clean in the graph induced on $R$. Then for all $v,w\in C$,
--   $$w \text{ is } 3\delta\text{-good with respect to } N^+_R(v) \text{ (in } R).$$
--   With $R=V$ and $C=C'_i$ a $\delta$-clean cluster of $\mathrm{OPT}'$, this is the paper's statement: any vertex $w\in C'_i$ is $3\delta$-good w.r.t. $N^+(v)$.
--
--   The lemma is the base case of the induction in Theorem 7's proof: when Cautious picks a vertex $v$ of a clean cluster, no vertex of that cluster is removed from $N^+(v)$ at the start of the removal step. The proof of Theorem 7 applies it in the remaining graph, hence the set $R$.
--
--   Differences from the source:
--   - generalization: C′ᵢ a δ-clean cluster of OPT′ in G → any set C ⊆ R that is δ-clean in the graph induced on any vertex set R; reason: the proof uses only that C is δ-clean; R = V and C = C′ᵢ is the page's statement.
-- source:
--   Bansal, Blum, Chawla, Correlation Clustering, Machine Learning 56 (2004) 89–113, p. 97, Lemma 8 (δ = 1/44 from p. 97)

import Mathlib
import Definitions.Def_CorrClustBBC_Cautious_Setting

namespace CorrClustBBC.Cautious
theorem lemma_8 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R C : Finset V) (hCR : C ⊆ R) (hC : IsClean G R δ44 C) (v w : V) (hv : v ∈ C) (hw : w ∈ C) :
    IsGood G R (3 * δ44) (posNbhd G R v) w := by sorry
end CorrClustBBC.Cautious
