-- Prove2me | Theorems.Thm_ExpanderBIS_Colorings_lemma_27
-- name    : ExpanderBIS.Colorings.lemma_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:30.829975+00:00
-- url     : https://prove2.me/theorems/7c1a5f93-5843-4cc4-a567-3ec3bc59599a
-- title:
--   Lemma 27 — |χ_{A,B}(S)| ≤ |A|^m|B|^m (1 − 1/|A|)^{|∂S∩𝒪|}(1 − 1/|B|)^{|∂S∩ℰ|}(|A|/|B|)^{|S∩ℰ|−|S∩𝒪|}
-- statement:
--   Let $q \ge 3$ and let $G$ be a $\Delta$-regular bipartite graph with sides $\mathcal O, \mathcal E$ of size $m$. Let $(A,B)$ be a pattern with $A$ and $B$ nonempty, and let $S \subseteq V$. Then the number of proper colorings that disagree with $(A,B)$ exactly on $S$ satisfies
--   $$|\chi_{A,B}(S)| \le |A|^m|B|^m \Bigl(1 - \frac1{|A|}\Bigr)^{|\partial S \cap \mathcal O|} \Bigl(1 - \frac1{|B|}\Bigr)^{|\partial S \cap \mathcal E|} \Bigl(\frac{|A|}{|B|}\Bigr)^{|S \cap \mathcal E| - |S \cap \mathcal O|}.$$
--
--   The exponent $|S\cap\mathcal E| - |S\cap\mathcal O|$ is an integer that may be negative. This bound is what makes the weights of large polymers small: every boundary vertex of $S$ costs a factor $1 - 1/|A|$ or $1 - 1/|B|$.
--
--   **Formalization Note.** The hypotheses $A \ne \emptyset$ and $B \ne \emptyset$ are added: the bound divides by $|A|$ and $|B|$, and for a pattern with an empty side it is false under Lean's $x/0 = 0$ (for $A = \emptyset$ and $S = \mathcal O$ the left side counts every proper coloring while the right side is $0$). The exponent is an integer power (`zpow`) in $\mathbb R$.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 26, Lemma 27

import Mathlib
import Definitions.Def_ExpanderBIS_Colorings_Setting

open Classical Finset

namespace ExpanderBIS.Colorings

theorem lemma_27 {m Δ q : ℕ} (hq : 3 ≤ q) (G : SimpleGraph (ExpanderBIS.RandomHardCore.Vertex m))
    (hG : G ∈ ExpanderBIS.RandomHardCore.Gbip m Δ) (A : Finset (Fin q)) (hA : A.Nonempty)
    (hB : (univ \ A).Nonempty) (S : Finset (ExpanderBIS.RandomHardCore.Vertex m)) :
    ((chi G q A S).card : ℝ) ≤
      (A.card : ℝ) ^ m * ((univ \ A).card : ℝ) ^ m *
        (1 - 1 / (A.card : ℝ)) ^ (ExpanderBIS.RandomHardCore.vertexBoundary G S ∩ ExpanderBIS.RandomHardCore.oddSide m).card *
        (1 - 1 / ((univ \ A).card : ℝ)) ^ (ExpanderBIS.RandomHardCore.vertexBoundary G S ∩ ExpanderBIS.RandomHardCore.evenSide m).card *
        ((A.card : ℝ) / (univ \ A).card) ^
          (((S ∩ ExpanderBIS.RandomHardCore.evenSide m).card : ℤ) - (S ∩ ExpanderBIS.RandomHardCore.oddSide m).card) := by sorry

end ExpanderBIS.Colorings
