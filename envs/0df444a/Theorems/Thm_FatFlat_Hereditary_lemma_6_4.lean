-- Prove2me | Theorems.Thm_FatFlat_Hereditary_lemma_6_4
-- name    : FatFlat.Hereditary.lemma_6_4
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-09T18:44:22.476598+00:00
-- url     : https://prove2.me/theorems/f0cb049f-9fbb-4639-98cd-c57f0ce75527
-- title:
--   Lemma 6.4 (Fan lemma) — many vertices near $o$ contain the leaves of an $\ell$-fan, $1\le\ell\le r$
-- statement:
--   For every $r\in\mathbb N$ there is a function $F:\mathbb N\to\mathbb N$ with the following property. Let $G$ be a finite graph, $o\in V(G)$, $m\in\mathbb N$, and $X\subseteq V(G)$ a set of at least $F(m)$ vertices, each at distance at most $r$ from $o$. Then there are $X'\subseteq X$ with $|X'|=m$ and an integer $\ell$ with $1\le\ell\le r$ such that $G$ contains an $\ell$-fan with leaf set $X'$ (with some center).
--
--   Differences from the source: none.
-- source:
--   Filtser, Le, Mählmann, Ma. Pilipczuk, Mi. Pilipczuk, Fatness and Flatness, arXiv:2607.21474, Lemma 6.4, p. 18 (PDF p. 20). Verbatim: 'Lemma 6.4 (Fan lemma). For every r ∈ N there exists a function F : N → N with the following property. Let G be a graph, o ∈ V(G), m ∈ N, and X ⊆ V(G) be a set of at least F(m) vertices, each at distance at most r from o. Then there are X′ ⊆ X of size m and 1 ⩽ ℓ ⩽ r, such that G contains an ℓ-fan with leaf set X′.' PDF SHA-256: 757d7502abd8762f687daa2125d7908bd129bcf2f5d6d5cc1756b514302adaf1.

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Classes

set_option autoImplicit false

namespace FatFlat.Hereditary

/-- **Lemma 6.4** (Fan lemma; arXiv:2607.21474, p. 18). For every `r ∈ ℕ` there is
`F : ℕ → ℕ` such that: for every graph `G`, `o ∈ V(G)`, `m ∈ ℕ` and set `X` of at least `F(m)`
vertices, each at distance at most `r` from `o`, there are `X′ ⊆ X` of size `m` and
`1 ≤ ℓ ≤ r` such that `G` contains an `ℓ`-fan with leaf set `X′`. -/
theorem lemma_6_4 (r : ℕ) : ∃ F : ℕ → ℕ, ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (o : V)
    (m : ℕ) (X : Finset V), F m ≤ X.card → (∀ x ∈ X, G.edist o x ≤ r) →
    ∃ X' : Finset V, X' ⊆ X ∧ X'.card = m ∧
      ∃ ℓ : ℕ, 1 ≤ ℓ ∧ ℓ ≤ r ∧ HasFan G ℓ (X' : Set V) := by sorry

end FatFlat.Hereditary
