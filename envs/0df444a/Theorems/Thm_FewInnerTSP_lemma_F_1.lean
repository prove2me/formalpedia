-- Prove2me | Theorems.Thm_FewInnerTSP_lemma_F_1
-- name    : FewInnerTSP.lemma_F_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:29:42.757289+00:00
-- url     : https://prove2.me/theorems/b81af606-a499-43bf-a6d2-9c9ec6d61a12
-- title:
--   Lemma F.1 (A uniform square packing constant)
-- statement:
--   Let $P$ be $n\ge3$ points in the plane and $T$ a shortest Euclidean tour of $P$. For every closed axis-aligned square $D$ of side $s>0$, at most
--   $$p_0=32768$$
--   edges of $T$ have length at least $s$ and exactly one endpoint in $D$. The same bound holds for every subset of the edges of $T$; that is, the edge set of $T$ and every subset of it are packing-compliant.
--
--   This is the explicit packing constant behind every cap of the separator: through constant covers it bounds long straddling edges and the edges of each owner frame by $\lambda=400p_0$.
--
--   Differences from the source:
--   - generalization: T a shortest tour of a general-position instance → any P : Fin n → ℝ² with n ≥ 3, no general position; reason: the exchange proof uses only that the four endpoints are distinct as indices, which the cycle structure gives; it specializes to the page's instances
--   - encoding: an axis-aligned square D of side s > 0; exactly one endpoint in D → closed squares; an edge {a, b} with P a ∈ D and P b ∉ D; reason: the page does not fix the boundary convention; closed squares are what Definition 3.4 is used with
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), Lemma F.1, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_FewInnerTSP_Packing

namespace FewInnerTSP

/-- **Lemma F.1 (A uniform square packing constant).** Li, Ma, Gong, *Exact Euclidean TSP with Few
Interior Points: A Square-Root Exponent*, STOC 2027 submission (manuscript sha256 6541f631…), Lemma F.1,
p.22 (PDF p.24): "Let T be a shortest Euclidean Hamiltonian cycle. For any axis-aligned square D of side
s > 0, at most p0 = 32768 edges of T have length at least s and exactly one endpoint in D. The same bound
holds for every subset of these edges."

For every `n ≥ 3`, every `P : Fin n → ℝ²` and every shortest tour `π`, the edge set of `π` is
packing-compliant with `p₀ = 32768` (every closed axis-aligned square of side `s > 0` has at most `p₀`
tour edges of length `≥ s` with exactly one endpoint in it), and so is every subset of it.

**Formalization Note** No general position is assumed: the exchange argument of App. F uses only that
the four endpoints are distinct as indices, which the cycle structure gives, and the strict decrease does
not need distinct points. -/
theorem lemma_F_1 (n : ℕ) (hn : 3 ≤ n) (P : Fin n → Pt) (π : Equiv.Perm (Fin n))
    (hπ : IsShortestTour P π) :
    IsPackingCompliant P (tourEdges π) ∧
      ∀ F : Finset (Sym2 (Fin n)), F ⊆ tourEdges π → IsPackingCompliant P F := by sorry

end FewInnerTSP
