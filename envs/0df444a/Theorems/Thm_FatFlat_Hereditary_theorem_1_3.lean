-- Prove2me | Theorems.Thm_FatFlat_Hereditary_theorem_1_3
-- name    : FatFlat.Hereditary.theorem_1_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-09T18:44:16.978309+00:00
-- url     : https://prove2.me/theorems/5f9dd408-f836-42f2-ba89-b929269465f0
-- title:
--   Theorem 1.3 — excluding a 3d-shallow induced 1-subdivided $K_h$ gives $(2d,37)$-drill-flatness with budget $hd$ and overhead $m^{2^{O(hd)}}$
-- statement:
--   There is a universal constant $c\in\mathbb N$ such that for all positive integers $h$ and $d$ there is a function $N:\mathbb N\to\mathbb N$ with:
--   1. every finite graph $G$ that does not contain the 1-subdivision of $K_h$ as a $3d$-shallow induced minor is $(2d,37)$-drill-flat with overhead $N$ and budget $hd$; and
--   2. (Moreover) $N(m)\le m^{2^{c\,h\,d}}$ for every $m\in\mathbb N$.
--
--   The same $N$ serves every such $G$; $c$ is chosen before $h$ and $d$.
--
--   Differences from the source:
--   - encoding: N(m) ⩽ m^{2^{O(hd)}} → ∃ c : ℕ (before h and d), ∀ m, N m ≤ m ^ 2 ^ (c * (h * d)); reason: O(hd) with h, d ≥ 1 is at most c·hd for one universal c, and a real c may be rounded up since m^(2^x) is nondecreasing in x for m ≥ 1 (and is 0 at m = 0)
-- source:
--   Filtser, Le, Mählmann, Ma. Pilipczuk, Mi. Pilipczuk, Fatness and Flatness, arXiv:2607.21474, Theorem 1.3, p. 4 (PDF p. 6); restated p. 11 (PDF 13), proof pp. 15–16 (PDF 17–18). Verbatim: 'Theorem 1.3 (Drill-flatness in induced-minor-free graphs). For all positive integers h and d, there exists a function N : N → N such that every graph G that does not contain the 1-subdivision of K_h as a 3d-shallow induced minor is (2d,37)-drill-flat with overhead N and budget hd. Moreover, N(m) ⩽ m^{2^{O(hd)}}.' PDF SHA-256: 757d7502abd8762f687daa2125d7908bd129bcf2f5d6d5cc1756b514302adaf1.

import Mathlib
import Definitions.Def_FatFlat_Hereditary_Basic
import Definitions.Def_FatFlat_Hereditary_Minors
import Definitions.Def_FatFlat_Hereditary_Patterns
import Definitions.Def_FatFlat_Hereditary_Classes

set_option autoImplicit false

namespace FatFlat.Hereditary

/-- **Theorem 1.3** (Drill-flatness in induced-minor-free graphs; arXiv:2607.21474, p. 4,
restated p. 11). For all positive integers `h` and `d` there is `N : ℕ → ℕ` such that every
graph `G` that does not contain the 1-subdivision of `K_h` as a `3d`-shallow induced minor is
`(2d, 37)`-drill-flat with overhead `N` and budget `hd`. Moreover `N(m) ≤ m^{2^{O(hd)}}`: one
universal constant `c`, chosen before `h` and `d`, gives `N(m) ≤ m^{2^{c·h·d}}` for all `m`. -/
theorem theorem_1_3 : ∃ c : ℕ, ∀ h d : ℕ, 0 < h → 0 < d → ∃ N : ℕ → ℕ,
    (∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      ¬ IsShallowInducedMinor (oneSubdivision (⊤ : SimpleGraph (Fin h))) G (3 * d) →
      IsDrillFlat G (2 * d) 37 N (h * d)) ∧
    ∀ m : ℕ, N m ≤ m ^ (2 ^ (c * (h * d))) := by sorry

end FatFlat.Hereditary
