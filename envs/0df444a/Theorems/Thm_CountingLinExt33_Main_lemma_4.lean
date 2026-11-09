-- Prove2me | Theorems.Thm_CountingLinExt33_Main_lemma_4
-- name    : CountingLinExt33.Main.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:01:28.610174+00:00
-- url     : https://prove2.me/theorems/0c645549-7caf-434e-a9b9-ac9037e3fb23
-- title:
--   Lemma 4 — realizable choices are determined by multiplicities
-- statement:
--   Let $Y$ be a finite set and $S_1,\ldots,S_t$ nonempty subsets of $Y$. A choice tuple $g=(g_i)_{i=1}^t$ is realizable if some total order of $Y$ makes $g_i$ the minimum of $S_i$ for every $i$. Define $m_y(g)=|\{i:g_i=y\}|$.
--
--   For any two realizable tuples $g,g'$, possibly witnessed by different total orders,
--
--   $$\bigl(\forall y\in Y,\ m_y(g)=m_y(g')\bigr)\ \Longrightarrow\ g=g'.$$
--
--   This injectivity prevents distinct compatible patterns from sharing a multiplicity vector. The family of subsets may be empty.
--
--   **Formalization Note** A ranking bijection to the numeric positions represents a total order; each tuple has its own existential ranking witness.
--
--   Differences from the source:
--   - encoding: a finite set Y and a t-element family → Fin m and Fin t, including zero sizes; reason: relabeling covers every finite set and family
--   - encoding: a witnessing total order for each realizable tuple → a separately quantified ranking bijection for each tuple; reason: ranking bijections represent all finite total orders without imposing a common order
-- source:
--   Keigo Oka, STOC 2027 submission #725 (October 2026), printed p. 4 (PDF p. 5), Lemma 4

import Definitions.Def_CountingLinExt33_Main_Orders

namespace CountingLinExt33.Main

/-- Keigo Oka, STOC 2027 submission #725 (October 2026), printed p.4 / PDF p.5, Lemma 4. -/
theorem lemma_4 (m t : ℕ) (S : Fin t → Finset (Fin m))
    (hS : ∀ i, (S i).Nonempty) (g g' : Fin t → Fin m)
    (hg : Realizable S g) (hg' : Realizable S g')
    (hm : ∀ y, multiplicity g y = multiplicity g' y) : g = g' := by sorry

end CountingLinExt33.Main
