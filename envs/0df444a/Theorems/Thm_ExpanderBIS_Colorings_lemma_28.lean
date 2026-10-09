-- Prove2me | Theorems.Thm_ExpanderBIS_Colorings_lemma_28
-- name    : ExpanderBIS.Colorings.lemma_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:47.962979+00:00
-- url     : https://prove2.me/theorems/f18598f6-9088-4109-8dd2-e637b2d9df5b
-- title:
--   Lemma 28 — every proper coloring lies in χ_{A,B}(S) for some pattern (A, B) and some little S
-- statement:
--   Let $q \ge 3$, $\Delta \ge 3$, and let $G$ be a $\Delta$-regular bipartite graph with sides of size $m$ that is a $\bigl(\frac{4\log\Delta}{\Delta}, \frac{\Delta}{4\log\Delta} - \frac12\bigr)$-expander. Then for every proper $q$-coloring $f$ of $G$ there are a pattern $(A,B)$ and a little set $S \subseteq V$, that is
--   $$|S| \le 4q\,\frac{\log\Delta}{\Delta}\, m,$$
--   such that $f \in \chi_{A,B}(S)$.
--
--   In words: on a strong expander every proper coloring is, outside a little set, an $(A,B)$-coloring for some pattern. The patterns play the role of ground states, and Lemma 28 says that the $\chi_{A,B}(S)$ with $S$ little cover all of $\mathcal X_q(G)$.
--
--   **Formalization Note.** The hypothesis $\Delta \ge 3$ is the paper's standing convention (§1.3, p. 5: "We take $\Delta \ge 3$ in all of our theorems"); without it the statement fails for $\Delta = 1$, where little sets are empty and a perfect matching has proper colorings matching no pattern.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 27, Lemma 28 (standing assumptions of §5, p. 26; Δ ≥ 3 from §1.3, p. 5)

import Mathlib
import Definitions.Def_ExpanderBIS_Colorings_Setting

open Classical Finset

namespace ExpanderBIS.Colorings

theorem lemma_28 {m Δ q : ℕ} (hq : 3 ≤ q) (hΔ : 3 ≤ Δ) (G : SimpleGraph (ExpanderBIS.RandomHardCore.Vertex m))
    (hG : G ∈ ExpanderBIS.RandomHardCore.Gbip m Δ) (hexp : ExpanderBIS.RandomHardCore.IsStdExpander G Δ) :
    ∀ f ∈ properColorings G q, ∃ A : Finset (Fin q), ∃ S : Finset (ExpanderBIS.RandomHardCore.Vertex m),
      IsLittle q Δ S ∧ f ∈ chi G q A S := by sorry

end ExpanderBIS.Colorings
