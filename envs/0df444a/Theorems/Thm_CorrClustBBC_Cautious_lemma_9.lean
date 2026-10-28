-- Prove2me | Theorems.Thm_CorrClustBBC_Cautious_lemma_9
-- name    : CorrClustBBC.Cautious.lemma_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:26:40.522239+00:00
-- url     : https://prove2.me/theorems/ea8dadfb-ebbb-4663-9bb2-3a7fd6be39ad
-- title:
--   Lemma 9, p. 98 — vertices of two distinct δ-clean clusters are never both 3δ-good w.r.t. one set X (δ = 1/44)
-- statement:
--   Let $\delta=1/44$. Let $G$ be a complete $\pm$-labelled graph on a finite vertex set $V$, let $R\subseteq V$, and let $C,C'\subseteq R$ be disjoint sets, both $\delta$-clean in the graph induced on $R$. For every $X\subseteq R$, every $v_1\in C$ and every $v_2\in C'$,
--   $$\neg\big(v_1 \text{ and } v_2 \text{ are both } 3\delta\text{-good with respect to } X\big).$$
--   With $R=V$ and $C=C'_i$, $C'=C'_j$ ($i\ne j$) two clusters of $\mathrm{OPT}'$, this is the paper's statement.
--
--   The lemma yields Corollary 10: the removal step never leaves vertices of two different clean clusters together.
--
--   Differences from the source:
--   - generalization: C′ᵢ, C′ⱼ (i ≠ j) clusters of OPT′ in G and an arbitrary set X → any two disjoint sets C, C′ ⊆ R that are δ-clean in the graph induced on any vertex set R, and any X ⊆ R; reason: the proof uses only cleanliness and disjointness; R = V (so every X qualifies) and C = C′ᵢ, C′ = C′ⱼ is the page's statement.
-- source:
--   Bansal, Blum, Chawla, Correlation Clustering, Machine Learning 56 (2004) 89–113, p. 98, Lemma 9 (δ = 1/44 from p. 97)

import Mathlib
import Definitions.Def_CorrClustBBC_Cautious_Setting

namespace CorrClustBBC.Cautious
theorem lemma_9 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R X C C' : Finset V) (hX : X ⊆ R) (hCR : C ⊆ R) (hC'R : C' ⊆ R) (hdisj : Disjoint C C')
    (hC : IsClean G R δ44 C) (hC' : IsClean G R δ44 C') (v₁ v₂ : V) (hv₁ : v₁ ∈ C) (hv₂ : v₂ ∈ C') :
    ¬ (IsGood G R (3 * δ44) X v₁ ∧ IsGood G R (3 * δ44) X v₂) := by sorry
end CorrClustBBC.Cautious
