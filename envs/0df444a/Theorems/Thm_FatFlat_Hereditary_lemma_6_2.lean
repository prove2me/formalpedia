-- Prove2me | Theorems.Thm_FatFlat_Hereditary_lemma_6_2
-- name    : FatFlat.Hereditary.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T18:44:44.457918+00:00
-- url     : https://prove2.me/theorems/bc8ff328-eea5-4378-88ce-2f867b7922f0
-- title:
--   Lemma 6.2 — a $d$-shallow induced minor of a suitable $H$ yields an induced $K(r,m)$ or $W(r,m)$ with $3\le r\le R(d)$
-- statement:
--   There is a function $R:\mathbb N\to\mathbb N$ such that for all $d,m\in\mathbb N$ there is a finite graph $H$ with the following property: if a finite graph $G$ contains $H$ as a $d$-shallow induced minor, then there is $r$ with $3\le r\le R(d)$ such that $G$ contains $K(r,m)$ or $W(r,m)$ as an induced subgraph.
--
--   Differences from the source:
--   - encoding: a graph H → a graph H on Fin n for some n; reason: shallow induced minor containment is invariant under isomorphism
-- source:
--   Filtser, Le, Mählmann, Ma. Pilipczuk, Mi. Pilipczuk, Fatness and Flatness, arXiv:2607.21474, Lemma 6.2, p. 17 (PDF p. 19). Verbatim: 'Lemma 6.2. There is a function R : N → N, such that for all d, m ∈ N there is a graph H with the following property. If a graph G contains H as a d-shallow induced minor, then there is 3 ⩽ r ⩽ R(d) such that G contains K(r, m) or W(r, m) as an induced subgraph.' PDF SHA-256: 757d7502abd8762f687daa2125d7908bd129bcf2f5d6d5cc1756b514302adaf1.

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Classes

set_option autoImplicit false

namespace FatFlat.Hereditary

/-- **Lemma 6.2** (arXiv:2607.21474, p. 17). There is `R : ℕ → ℕ` such that for all `d, m ∈ ℕ`
there is a graph `H` with the following property: if a graph `G` contains `H` as a `d`-shallow
induced minor, then there is `3 ≤ r ≤ R(d)` such that `G` contains `K(r, m)` or `W(r, m)` as
an induced subgraph. -/
theorem lemma_6_2 : ∃ R : ℕ → ℕ, ∀ d m : ℕ, ∃ (n : ℕ) (H : SimpleGraph (Fin n)),
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsShallowInducedMinor H G d →
      ∃ r : ℕ, 3 ≤ r ∧ r ≤ R d ∧
        (Nonempty (subdividedClique r m ↪g G) ∨ Nonempty (web r m ↪g G)) := by sorry

end FatFlat.Hereditary
