-- Prove2me | Theorems.Thm_ExpanderBIS_RandomHardCore_lemma_24
-- name    : ExpanderBIS.RandomHardCore.lemma_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:06.917242+00:00
-- url     : https://prove2.me/theorems/eee1346a-be7d-4fe6-939d-c1d92ec03e96
-- title:
--   Lemma 24 — an independent set is tiny on at least one side
-- statement:
--   For all sufficiently large $\Delta$ and all sufficiently large $m$ (depending on $\Delta$), let $G$ be a $\Delta$-regular bipartite $(4\log\Delta/\Delta,\Delta/(4\log\Delta)-1/2)$-expander on two sides $\mathcal O,\mathcal E$ of size $m$. If $I$ is an independent set, then
--
--   $$|I\cap\mathcal O|\le\frac{4\log\Delta}{\Delta}m\quad\text{or}\quad |I\cap\mathcal E|\le\frac{4\log\Delta}{\Delta}m.$$
--
--   This dichotomy assigns every independent set to at least one of the two polymer models.
--
--   **Formalization Note** The page states the lemma for every $m$; its proof applies the expansion property to a subset of size exactly $(4\log\Delta/\Delta)m$, which need not be an integer. As printed, the lemma is false for small $m$: $G=K_{m,m}$ minus $b$ disjoint copies of $K_{r,r}$ ($m=br$, $\Delta=(b-1)r$), e.g. $\Delta=442$, $m=468$, $r=26$, is a standard expander, and the block $\mathcal O_1\cup\mathcal E_1$ is an independent set with $r=26>(4\log\Delta/\Delta)m\approx25.8$ vertices on each side; the same family gives counterexamples for arbitrarily large $\Delta$. The statement therefore carries a graph-size threshold $m_0$ depending on $\Delta$ (the rounded argument closes once $m\ge\Delta^2$). Theorem 2 only uses the lemma as $m\to\infty$. The degree threshold $\Delta_0$ spells out the large-degree regime of §4.4.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, pp. 23–24, standing assumption and Lemma 24

import Mathlib
import Definitions.Def_ExpanderBIS_RandomHardCore_Setting

namespace ExpanderBIS.RandomHardCore

theorem lemma_24 :
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ G : SimpleGraph (Vertex m), G ∈ Gbip m Δ → IsStdExpander G Δ →
        ∀ I : Finset (Vertex m), IsIndependent G I →
          IsTiny Δ (I ∩ oddSide m) ∨ IsTiny Δ (I ∩ evenSide m) := by sorry

end ExpanderBIS.RandomHardCore
